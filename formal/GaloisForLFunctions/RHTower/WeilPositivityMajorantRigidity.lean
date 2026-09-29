import GaloisForLFunctions.RHTower.WeilFullConeRiemannKernelRigidity
import GaloisForLFunctions.RHTower.WeilSymbolMertensExpansion
import GaloisForLFunctions.RHTower.WeilPositivityLogDensityMaximality
import GaloisForLFunctions.RHTower.WeilPositivityFiniteLevelExistence
import GaloisForLFunctions.RHTower.ZetaZeroFreeRegionUnrestricted

/-!
# No Weil-positive weight system majorizes `Λ`

**Theorem** (`eq_vonMangoldt_of_weilPositive_of_ge`, unconditional). If the weights `lam` are
Weil-positive (nonnegative finite-atom symbol energy on every polar-constrained `C²` test at every
level) and `lam(n) ≥ Λ(n)` for all `n ≥ 2`, then `lam(n) = Λ(n)` for all `n ≥ 2`.

The test is a polar second difference of the truncated Riemann kernel `u = Φχ_L`:
`f = u − α u(· − c) − α u(· + c)` with `α = 1/(2 cosh(c/2))` (`polarRiemannDifference`). Its
transform is `(1 − 2α cos(cz)) û(z)`: it vanishes at `z = ±i/2`, so `f` is polar, and it is at most
`3|û(z)|` in the critical strip, so `f` stays near the radical of the zero side
(`norm_W_polarRiemannDifference_le`).

With `w = lam − Λ ≥ 0` and `k` the autocorrelation of `Φχ_L`, the energy of `f` is
`2π Re W(f, f) − 2π Σ_n w(n) n^{−1/2} (k_f(log n) + k_f(−log n))`, and
`k_f(y) ≥ k(y) − 2α (k(y − c) + k(y + c))` with `k ≥ 0`. An atom `w(n₀) > 0` contributes
`≥ w(n₀) n₀^{−1/2} k(log n₀) > 0`. The subtracted terms are at most
`8 C Σ_n (w(n)/n) e^{−|log n − c|}`, a smoothing of the excess measure `w(n)/n` at scale `c`.
The log-density bound for supersystems (`weil_supersystem_excess_small`) gives
`Σ_{n ≤ K} w(n)/n = o(log K)`, so averaging over `c ∈ [M, 2M]` finds a shift where the smoothing
is small (`exists_mul_excessSmoothing_le`).
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate
open Zeta23

namespace RHTower

noncomputable section

/-! ## The polar weight -/

/-- The weight `α = 1/(2 cosh(c/2))` that makes `1 − α(e^{−c/2} + e^{c/2})` vanish. -/
def polarWeight (c : ℝ) : ℝ := 1 / (2 * Real.cosh (c / 2))

theorem polarWeight_pos (c : ℝ) : 0 < polarWeight c := by
  unfold polarWeight; have := Real.cosh_pos (c / 2); positivity

theorem polarWeight_mul_exp_add (c : ℝ) :
    polarWeight c * (Real.exp (-(c / 2)) + Real.exp (c / 2)) = 1 := by
  unfold polarWeight
  rw [Real.cosh_eq]
  have := Real.exp_pos (c / 2)
  have := Real.exp_pos (-(c / 2))
  field_simp
  ring

theorem polarWeight_mul_exp_le (c : ℝ) : polarWeight c * Real.exp (c / 2) ≤ 1 := by
  have h := polarWeight_mul_exp_add c
  have := polarWeight_pos c
  have := Real.exp_pos (-(c / 2))
  nlinarith

/-! ## The polar second difference of the truncated kernel -/

/-- The polar second difference `Φχ_L − α Φχ_L(· − c) − α Φχ_L(· + c)`. -/
def polarRiemannDifference (L c : ℝ) (u : ℝ) : ℂ :=
  truncatedRiemannKernel L u - (polarWeight c : ℂ) * truncatedRiemannKernel L (u - c) -
    (polarWeight c : ℂ) * truncatedRiemannKernel L (u - -c)

/-- Its real profile. -/
def polarRiemannDifferenceReal (L c : ℝ) (u : ℝ) : ℝ :=
  truncatedRiemannKernelReal L u - polarWeight c * truncatedRiemannKernelReal L (u - c) -
    polarWeight c * truncatedRiemannKernelReal L (u - -c)

theorem polarRiemannDifference_eq (L c : ℝ) :
    polarRiemannDifference L c = fun u => (polarRiemannDifferenceReal L c u : ℂ) := by
  funext u
  simp only [polarRiemannDifference, polarRiemannDifferenceReal, truncatedRiemannKernel_eq]
  push_cast
  ring

theorem continuous_truncatedRiemannKernel (L : ℝ) : Continuous (truncatedRiemannKernel L) :=
  (contDiff_nearRadicalTest L _).continuous

theorem hasCompactSupport_comp_sub {g : ℝ → ℂ} (hg : HasCompactSupport g) (s : ℝ) :
    HasCompactSupport fun u => g (u - s) :=
  hg.comp_homeomorph (Homeomorph.subRight s)

theorem contDiff_polarRiemannDifference (L c : ℝ) : ContDiff ℝ 2 (polarRiemannDifference L c) := by
  have h := contDiff_nearRadicalTest L (fun _ : Fin 1 => (1 : ℂ))
  have h1 : ContDiff ℝ 2 fun u : ℝ => truncatedRiemannKernel L (u - c) :=
    h.comp (contDiff_id.sub contDiff_const)
  have h2 : ContDiff ℝ 2 fun u : ℝ => truncatedRiemannKernel L (u - -c) :=
    h.comp (contDiff_id.sub contDiff_const)
  exact (h.sub (contDiff_const.mul h1)).sub (contDiff_const.mul h2)

theorem truncatedRiemannKernel_eq_zero {L u : ℝ} (hu : L < |u|) : truncatedRiemannKernel L u = 0 := by
  refine image_eq_zero_of_notMem_tsupport fun hmem => ?_
  have h := tsupport_nearRadicalTest L (fun _ : Fin 1 => (1 : ℂ)) hmem
  rw [mem_Icc] at h
  rcases le_or_gt 0 u with h0 | h0
  · rw [abs_of_nonneg h0] at hu; linarith [h.2]
  · rw [abs_of_neg h0] at hu; linarith [h.1]

theorem tsupport_polarRiemannDifference {L c : ℝ} (hc : 0 ≤ c) :
    tsupport (polarRiemannDifference L c) ⊆ Icc (-(L + c)) (L + c) := by
  refine tsupport_subset_of_vanish fun u hu => ?_
  have h0 : L < |u| := by linarith
  have h1 : L < |u - c| := by
    have := abs_sub_abs_le_abs_sub u c
    rw [abs_of_nonneg hc] at this; linarith
  have h2 : L < |u - -c| := by
    have := abs_sub_abs_le_abs_sub u (-c)
    rw [abs_neg, abs_of_nonneg hc] at this; linarith
  simp only [polarRiemannDifference, truncatedRiemannKernel_eq_zero h0,
    truncatedRiemannKernel_eq_zero h1, truncatedRiemannKernel_eq_zero h2, mul_zero, sub_zero]

theorem integrable_translate_mul_cexp (L s : ℝ) (z : ℂ) :
    Integrable fun u : ℝ => truncatedRiemannKernel L (u - s) * Complex.exp (I * z * u) :=
  ((continuous_truncatedRiemannKernel L).comp (continuous_id.sub continuous_const)).mul
    (by fun_prop) |>.integrable_of_hasCompactSupport
    ((hasCompactSupport_comp_sub (hasCompactSupport_truncatedRiemannKernel L) s).mul_right)

/-- The transform of the polar second difference: `(1 − α e^{izc} − α e^{−izc}) û(z)`. -/
theorem paperFT_polarRiemannDifference (L c : ℝ) (z : ℂ) :
    paperFT (polarRiemannDifference L c) z =
      (1 - (polarWeight c : ℂ) * Complex.exp (I * z * c) -
        (polarWeight c : ℂ) * Complex.exp (I * z * ((-c : ℝ) : ℂ))) *
        paperFT (truncatedRiemannKernel L) z := by
  have h0 : Integrable fun u : ℝ => truncatedRiemannKernel L u * Complex.exp (I * z * u) := by
    simpa using integrable_translate_mul_cexp L 0 z
  have h1 := integrable_translate_mul_cexp L c z
  have h2 := integrable_translate_mul_cexp L (-c) z
  have e1 := paperFT_comp_sub (truncatedRiemannKernel L) c z
  have e2 := paperFT_comp_sub (truncatedRiemannKernel L) (-c) z
  unfold paperFT at e1 e2 ⊢
  have hsplit : (fun u : ℝ => polarRiemannDifference L c u * Complex.exp (I * z * u)) =
      fun u : ℝ => (truncatedRiemannKernel L u * Complex.exp (I * z * u) -
        (polarWeight c : ℂ) * (truncatedRiemannKernel L (u - c) * Complex.exp (I * z * u))) -
        (polarWeight c : ℂ) * (truncatedRiemannKernel L (u - -c) * Complex.exp (I * z * u)) := by
    funext u; simp only [polarRiemannDifference]; ring
  have hA : Integrable fun u : ℝ => truncatedRiemannKernel L u * Complex.exp (I * z * u) -
      (polarWeight c : ℂ) * (truncatedRiemannKernel L (u - c) * Complex.exp (I * z * u)) :=
    h0.sub (h1.const_mul _)
  have hB : Integrable fun u : ℝ =>
      (polarWeight c : ℂ) * (truncatedRiemannKernel L (u - -c) * Complex.exp (I * z * u)) :=
    h2.const_mul _
  have hC : Integrable fun u : ℝ =>
      (polarWeight c : ℂ) * (truncatedRiemannKernel L (u - c) * Complex.exp (I * z * u)) :=
    h1.const_mul _
  beta_reduce at e1 e2
  rw [hsplit, integral_sub hA hB, integral_sub h0 hC, integral_const_mul, integral_const_mul, e1, e2]
  push_cast
  ring

/-- The polar second difference is polar. -/
theorem paperFT_polarRiemannDifference_pole (L c : ℝ) :
    paperFT (polarRiemannDifference L c) (I / 2) = 0 ∧
      paperFT (polarRiemannDifference L c) (-(I / 2)) = 0 := by
  have hk := polarWeight_mul_exp_add c
  have hk' : ((polarWeight c : ℝ) : ℂ) * ((Real.exp (-(c / 2)) : ℝ) + (Real.exp (c / 2) : ℝ)) = 1 := by
    exact_mod_cast hk
  have ha : I * (I / 2) * (c : ℂ) = ((-(c / 2) : ℝ) : ℂ) := by
    push_cast; ring_nf; rw [I_sq]; ring
  have hb : I * (I / 2) * ((-c : ℝ) : ℂ) = ((c / 2 : ℝ) : ℂ) := by
    push_cast; ring_nf; rw [I_sq]; ring
  have hc : I * (-(I / 2)) * (c : ℂ) = ((c / 2 : ℝ) : ℂ) := by
    push_cast; ring_nf; rw [I_sq]; ring
  have hd : I * (-(I / 2)) * ((-c : ℝ) : ℂ) = ((-(c / 2)) : ℝ) := by
    push_cast; ring_nf; rw [I_sq]; ring
  constructor
  · rw [paperFT_polarRiemannDifference, ha, hb, ← Complex.ofReal_exp, ← Complex.ofReal_exp]
    have : (1 : ℂ) - (polarWeight c : ℂ) * (Real.exp (-(c / 2)) : ℂ) -
        (polarWeight c : ℂ) * (Real.exp (c / 2) : ℂ) = 0 := by
      rw [← hk']; ring
    rw [this, zero_mul]
  · rw [paperFT_polarRiemannDifference, hc, hd, ← Complex.ofReal_exp, ← Complex.ofReal_exp]
    have : (1 : ℂ) - (polarWeight c : ℂ) * (Real.exp (c / 2) : ℂ) -
        (polarWeight c : ℂ) * (Real.exp (-(c / 2)) : ℂ) = 0 := by
      rw [← hk']; ring
    rw [this, zero_mul]

/-- In the critical strip the multiplier of the polar second difference has size at most `3`. -/
theorem norm_polarMultiplier_le {c : ℝ} (hc : 0 ≤ c) {z : ℂ} (hz : |z.im| ≤ 1 / 2) :
    ‖1 - (polarWeight c : ℂ) * Complex.exp (I * z * c) -
        (polarWeight c : ℂ) * Complex.exp (I * z * ((-c : ℝ) : ℂ))‖ ≤ 3 := by
  have hα := polarWeight_pos c
  have hbound : ∀ s : ℝ, |s| ≤ c →
      ‖(polarWeight c : ℂ) * Complex.exp (I * z * (s : ℂ))‖ ≤ 1 := by
    intro s hs
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hα.le, Complex.norm_exp]
    have hre : (I * z * (s : ℂ)).re = -(z.im * s) := by simp [Complex.mul_re]
    rw [hre]
    have h1 : -(z.im * s) ≤ c / 2 := by
      have := abs_mul z.im s
      have h2 : |z.im * s| ≤ 1 / 2 * c :=
        this ▸ mul_le_mul hz hs (abs_nonneg _) (by norm_num)
      have := neg_abs_le (z.im * s)
      have := le_abs_self (z.im * s)
      linarith
    calc polarWeight c * Real.exp (-(z.im * s)) ≤ polarWeight c * Real.exp (c / 2) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h1) hα.le
      _ ≤ 1 := polarWeight_mul_exp_le c
  have e1 := hbound c (by rw [abs_of_nonneg hc])
  have e2 := hbound (-c) (by rw [abs_neg, abs_of_nonneg hc])
  calc _ ≤ ‖(1 : ℂ) - (polarWeight c : ℂ) * Complex.exp (I * z * c)‖ +
        ‖(polarWeight c : ℂ) * Complex.exp (I * z * ((-c : ℝ) : ℂ))‖ := norm_sub_le _ _
    _ ≤ (‖(1 : ℂ)‖ + ‖(polarWeight c : ℂ) * Complex.exp (I * z * c)‖) +
        ‖(polarWeight c : ℂ) * Complex.exp (I * z * ((-c : ℝ) : ℂ))‖ := by
        gcongr; exact norm_sub_le _ _
    _ ≤ 3 := by rw [norm_one]; linarith

/-! ## The zero side of the polar second difference -/

/-- A zero-by-zero bound on the transform bounds the zero side. -/
theorem norm_W_le_of_zero_bound {f : ℝ → ℂ} {E : ℝ} (hE0 : 0 ≤ E)
    (hv : ∀ ρ : zetaZeroConfig.carrier,
      (1 + |(ρ : ℂ).im|) * ‖paperFT f (gammaOf ρ)‖ ≤ E ∧
        (1 + |(ρ : ℂ).im|) * ‖paperFT f ((starRingEnd ℂ) (gammaOf ρ))‖ ≤ E) :
    ‖zetaZeroConfig.W f f‖ ≤ (5 / 4) * zetaInvSqSum * E ^ 2 := by
  have hsum : Summable (fun ρ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))) := by
    have := WeilEF.zero_sum_inv_sq zetaSeam
    simpa [zetaZeroConfig] using this
  have hpt : ∀ ρ : zetaZeroConfig.carrier, ‖zetaZeroConfig.Wsummand f f ρ‖ ≤
      (5 / 4) * E ^ 2 * ((zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))) := by
    intro ρ
    have hstrip := zetaZeroConfig.strip ρ ρ.2
    obtain ⟨hv1, hv2⟩ := hv ρ
    have hq := one_div_one_add_abs_im_sq_le hstrip
    unfold ZeroConfig.Wsummand
    rw [norm_mul, norm_mul, Complex.norm_natCast, RCLike.norm_conj]
    have hm : (0 : ℝ) ≤ zetaZeroConfig.mult ρ := Nat.cast_nonneg _
    set x1 := ‖paperFT f (gammaOf ρ)‖
    set x2 := ‖paperFT f ((starRingEnd ℂ) (gammaOf ρ))‖
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
  have hsum' : Summable (fun ρ : zetaZeroConfig.carrier => ‖zetaZeroConfig.Wsummand f f ρ‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpt (hsum.mul_left _)
  unfold ZeroConfig.W
  refine (norm_tsum_le_tsum_norm hsum').trans ?_
  refine (Summable.tsum_le_tsum hpt hsum' (hsum.mul_left _)).trans (le_of_eq ?_)
  rw [tsum_mul_left, zetaInvSqSum]; ring

/-- The weighted tail integrals of the truncated kernel. -/
def truncatedRiemannTailEnergy (L : ℝ) : ℝ :=
  (∫ u : ℝ, ‖nearRadicalTail L (fun _ : Fin 1 => (1 : ℂ)) u‖ * Real.exp (1 / 2 * |u|)) +
    ∫ u : ℝ, ‖nearRadicalTailDeriv L (fun _ : Fin 1 => (1 : ℂ)) u‖ * Real.exp (1 / 2 * |u|)

theorem truncatedRiemannTailEnergy_nonneg (L : ℝ) : 0 ≤ truncatedRiemannTailEnergy L :=
  add_nonneg (integral_nonneg fun _ => by positivity) (integral_nonneg fun _ => by positivity)

/-- The truncated kernel is small at every zero, relative to the tail energy. -/
theorem truncatedRiemannKernel_zero_bound (L : ℝ) {Λ : ℝ}
    (hΛ : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ Λ) (ρ : zetaZeroConfig.carrier) :
    (1 + |(ρ : ℂ).im|) * ‖paperFT (truncatedRiemannKernel L) (gammaOf ρ)‖ ≤
        truncatedRiemannTailEnergy L ∧
      (1 + |(ρ : ℂ).im|) * ‖paperFT (truncatedRiemannKernel L) ((starRingEnd ℂ) (gammaOf ρ))‖ ≤
        truncatedRiemannTailEnergy L := by
  have hmem := ρ.2
  have hstrip' : 0 < (ρ : ℂ).re ∧ (ρ : ℂ).re < 1 := by
    have h : IsNontrivialZero (ρ : ℂ) := hmem
    exact ⟨h.2.1, h.2.2⟩
  have hIm : |(gammaOf (ρ : ℂ)).im| ≤ 1 / 2 := (WeilEF.abs_gammaOf_im_lt hstrip').le
  have hIm' : |((starRingEnd ℂ) (gammaOf (ρ : ℂ))).im| ≤ 1 / 2 := by
    rw [Complex.conj_im, abs_neg]; exact hIm
  obtain ⟨hz1, hz2⟩ := paperFT_kernelComb_at_zero (fun _ : Fin 1 => (1 : ℂ)) hmem
  constructor
  · rw [truncatedRiemannKernel, paperFT_nearRadicalTest_eq, hz1, zero_sub, norm_neg]
    have h := one_add_abs_re_mul_norm_paperFT_tail_le L (fun _ : Fin 1 => (1 : ℂ)) hΛ hIm
    rwa [WeilEF.gammaOf_re] at h
  · rw [truncatedRiemannKernel, paperFT_nearRadicalTest_eq, hz2, zero_sub, norm_neg]
    have h := one_add_abs_re_mul_norm_paperFT_tail_le L (fun _ : Fin 1 => (1 : ℂ)) hΛ hIm'
    rwa [Complex.conj_re, WeilEF.gammaOf_re] at h

/-- The zero side of the polar second difference is at most nine times the near-radical energy
of the truncated kernel. -/
theorem norm_W_polarRiemannDifference_le (L : ℝ) {c : ℝ} (hc : 0 ≤ c) {Λ : ℝ}
    (hΛ : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ Λ) :
    ‖zetaZeroConfig.W (polarRiemannDifference L c) (polarRiemannDifference L c)‖ ≤
      9 * ((5 / 4) * zetaInvSqSum * truncatedRiemannTailEnergy L ^ 2) := by
  have hE0 := truncatedRiemannTailEnergy_nonneg L
  have h := norm_W_le_of_zero_bound (f := polarRiemannDifference L c)
    (E := 3 * truncatedRiemannTailEnergy L) (by positivity) (fun ρ => ?_)
  · calc _ ≤ (5 / 4) * zetaInvSqSum * (3 * truncatedRiemannTailEnergy L) ^ 2 := h
      _ = 9 * ((5 / 4) * zetaInvSqSum * truncatedRiemannTailEnergy L ^ 2) := by ring
  have hmem := ρ.2
  have hstrip' : 0 < (ρ : ℂ).re ∧ (ρ : ℂ).re < 1 := by
    have h : IsNontrivialZero (ρ : ℂ) := hmem
    exact ⟨h.2.1, h.2.2⟩
  have hIm : |(gammaOf (ρ : ℂ)).im| ≤ 1 / 2 := (WeilEF.abs_gammaOf_im_lt hstrip').le
  have hIm' : |((starRingEnd ℂ) (gammaOf (ρ : ℂ))).im| ≤ 1 / 2 := by
    rw [Complex.conj_im, abs_neg]; exact hIm
  obtain ⟨hv1, hv2⟩ := truncatedRiemannKernel_zero_bound L hΛ ρ
  have hd : 0 ≤ 1 + |(ρ : ℂ).im| := by positivity
  constructor
  · rw [paperFT_polarRiemannDifference, norm_mul]
    have hm := norm_polarMultiplier_le hc hIm
    calc (1 + |(ρ : ℂ).im|) * (‖_‖ * ‖paperFT (truncatedRiemannKernel L) (gammaOf ρ)‖)
        = ‖1 - (polarWeight c : ℂ) * Complex.exp (I * gammaOf ρ * c) -
            (polarWeight c : ℂ) * Complex.exp (I * gammaOf ρ * ((-c : ℝ) : ℂ))‖ *
          ((1 + |(ρ : ℂ).im|) * ‖paperFT (truncatedRiemannKernel L) (gammaOf ρ)‖) := by ring
      _ ≤ 3 * truncatedRiemannTailEnergy L :=
          mul_le_mul hm hv1 (by positivity) (by norm_num)
  · rw [paperFT_polarRiemannDifference, norm_mul]
    have hm := norm_polarMultiplier_le hc hIm'
    calc (1 + |(ρ : ℂ).im|) * (‖_‖ *
          ‖paperFT (truncatedRiemannKernel L) ((starRingEnd ℂ) (gammaOf ρ))‖)
        = ‖1 - (polarWeight c : ℂ) * Complex.exp (I * (starRingEnd ℂ) (gammaOf ρ) * c) -
            (polarWeight c : ℂ) *
              Complex.exp (I * (starRingEnd ℂ) (gammaOf ρ) * ((-c : ℝ) : ℂ))‖ *
          ((1 + |(ρ : ℂ).im|) *
            ‖paperFT (truncatedRiemannKernel L) ((starRingEnd ℂ) (gammaOf ρ))‖) := by ring
      _ ≤ 3 * truncatedRiemannTailEnergy L :=
          mul_le_mul hm hv2 (by positivity) (by norm_num)

/-- The near-radical energy of the truncated kernel relative to its mass, as in
`norm_W_nearRadicalTest_le_ratio`. -/
theorem nearRadicalEnergy_le_ratio (L : ℝ) {Λ : ℝ}
    (hΛ : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ Λ)
    (hY₀ : 40 ≤ Real.exp (2 * (L - 1))) (hkY : ((0 + 2 : ℕ) : ℝ) + 1 ≤ Real.exp (2 * (L - 1)) / 10) :
    (5 / 4) * zetaInvSqSum * truncatedRiemannTailEnergy L ^ 2 ≤
      20 * zetaInvSqSum * (1 + 2 * Λ) ^ 2 *
        ((28 * ((0 + 2 : ℕ) : ℝ) * (16 * Real.exp 1) ^ (0 + 2) * Real.exp (2 * (L - 1)) ^ 2 *
            Real.exp (-π * Real.exp (2 * (L - 1)))) ^ 2 /
          (Real.exp (-π * Real.exp (2 * (L - 1)) / 2) / (176 * (8 * Real.exp 1) ^ (2 * (0 + 2))))) *
        ∫ u : ℝ, ‖truncatedRiemannKernel L u‖ ^ 2 := by
  set a : Fin (0 + 1) → ℂ := fun _ => 1 with hadef
  set Y₀ := Real.exp (2 * (L - 1)) with hY₀def
  have hYpos : 0 < Y₀ := Real.exp_pos _
  have hΛ0 : 0 ≤ Λ := (abs_nonneg _).trans (hΛ 0)
  set Kt := 28 * ((0 + 2 : ℕ) : ℝ) * (16 * Real.exp 1) ^ (0 + 2) * Y₀ ^ 2 * Real.exp (-π * Y₀)
    with hKt
  set Kb := Real.exp (-π * Y₀ / 2) / (176 * (8 * Real.exp 1) ^ (2 * (0 + 2))) with hKb
  have hKt0 : 0 ≤ Kt := by rw [hKt]; positivity
  have hKb0 : 0 < Kb := by rw [hKb]; positivity
  obtain ⟨z₁, hz₁, h₁⟩ := exists_bulk_max (kernelPoly fun i => (a i).re) hYpos
  obtain ⟨z₂, hz₂, h₂⟩ := exists_bulk_max (kernelPoly fun i => (a i).im) hYpos
  obtain ⟨z₃, hz₃, h₃⟩ := exists_bulk_max (kernelPoly (parityCoeff fun i => (a i).re)) hYpos
  obtain ⟨z₄, hz₄, h₄⟩ := exists_bulk_max (kernelPoly (parityCoeff fun i => (a i).im)) hYpos
  set M₁ := |(kernelPoly fun i => (a i).re).eval z₁|
  set M₂ := |(kernelPoly fun i => (a i).im).eval z₂|
  set M₃ := |(kernelPoly (parityCoeff fun i => (a i).re)).eval z₃|
  set M₄ := |(kernelPoly (parityCoeff fun i => (a i).im)).eval z₄|
  have hpt := nearRadicalTail_pointwise_le L a hΛ (by linarith) hkY h₁ h₂ h₃ h₄
  have hE := nearRadicalTail_integrals_le L a hΛ (C := (1 + 2 * Λ) * Kt * (M₁ + M₂ + M₃ + M₄)) hpt
  have hbulk := integral_norm_sq_nearRadicalTest_ge L a hY₀ hkY hz₁ hz₂ hz₃ hz₄ h₁ h₂ h₃ h₄
  have hS := zetaInvSqSum_nonneg
  set E := truncatedRiemannTailEnergy L with hEdef
  have hE0 : 0 ≤ E := truncatedRiemannTailEnergy_nonneg L
  have hE' : E ≤ 2 * ((1 + 2 * Λ) * Kt * (M₁ + M₂ + M₃ + M₄)) := hE
  have hm1 : 0 ≤ M₁ := abs_nonneg _
  have hm2 : 0 ≤ M₂ := abs_nonneg _
  have hm3 : 0 ≤ M₃ := abs_nonneg _
  have hm4 : 0 ≤ M₄ := abs_nonneg _
  have hsq : (M₁ + M₂ + M₃ + M₄) ^ 2 ≤ 4 * (M₁ ^ 2 + M₂ ^ 2 + M₃ ^ 2 + M₄ ^ 2) := by
    nlinarith [sq_nonneg (M₁ - M₂), sq_nonneg (M₁ - M₃), sq_nonneg (M₁ - M₄),
      sq_nonneg (M₂ - M₃), sq_nonneg (M₂ - M₄), sq_nonneg (M₃ - M₄)]
  have hE2 : E ^ 2 ≤ 16 * (1 + 2 * Λ) ^ 2 * Kt ^ 2 * (M₁ ^ 2 + M₂ ^ 2 + M₃ ^ 2 + M₄ ^ 2) := by
    calc E ^ 2 ≤ (2 * ((1 + 2 * Λ) * Kt * (M₁ + M₂ + M₃ + M₄))) ^ 2 := pow_le_pow_left₀ hE0 hE' 2
      _ = 4 * (1 + 2 * Λ) ^ 2 * Kt ^ 2 * (M₁ + M₂ + M₃ + M₄) ^ 2 := by ring
      _ ≤ 4 * (1 + 2 * Λ) ^ 2 * Kt ^ 2 * (4 * (M₁ ^ 2 + M₂ ^ 2 + M₃ ^ 2 + M₄ ^ 2)) := by gcongr
      _ = _ := by ring
  have hbulk' : Kb * (M₁ ^ 2 + M₂ ^ 2 + M₃ ^ 2 + M₄ ^ 2) ≤
      ∫ u : ℝ, ‖truncatedRiemannKernel L u‖ ^ 2 := hbulk
  have hMsq : M₁ ^ 2 + M₂ ^ 2 + M₃ ^ 2 + M₄ ^ 2 ≤
      (∫ u : ℝ, ‖truncatedRiemannKernel L u‖ ^ 2) / Kb := by
    rw [le_div_iff₀ hKb0]; linarith
  calc (5 / 4) * zetaInvSqSum * E ^ 2
      ≤ (5 / 4) * zetaInvSqSum *
          (16 * (1 + 2 * Λ) ^ 2 * Kt ^ 2 * (M₁ ^ 2 + M₂ ^ 2 + M₃ ^ 2 + M₄ ^ 2)) := by gcongr
    _ ≤ (5 / 4) * zetaInvSqSum *
          (16 * (1 + 2 * Λ) ^ 2 * Kt ^ 2 * ((∫ u : ℝ, ‖truncatedRiemannKernel L u‖ ^ 2) / Kb)) := by
        gcongr
    _ = 20 * zetaInvSqSum * (1 + 2 * Λ) ^ 2 * (Kt ^ 2 / Kb) *
          ∫ u : ℝ, ‖truncatedRiemannKernel L u‖ ^ 2 := by ring

/-- The near-radical energy of `Φχ_L` tends to zero. -/
theorem exists_nearRadicalEnergy_le {ε : ℝ} (hε : 0 < ε) :
    ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
      (5 / 4) * zetaInvSqSum * truncatedRiemannTailEnergy L ^ 2 ≤ ε := by
  obtain ⟨Λ, hΛ0, hΛ⟩ := GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition
  obtain ⟨M, hM0, hM⟩ := exists_integral_norm_sq_truncatedRiemannKernel_le
  set S := zetaInvSqSum with hS
  have hS0 : 0 ≤ S := zetaInvSqSum_nonneg
  set Ystar := max (max 100 (Real.log (720 * nearRadicalConst S Λ + 1)))
    (Real.log ((M + 1) / ε)) with hYstar
  refine ⟨1 + |Real.log Ystar| / 2 + 1, fun L hL => ?_⟩
  set Y₀ := Real.exp (2 * (L - 1)) with hY₀def
  have hYstar_pos : 0 < Ystar :=
    lt_of_lt_of_le (by norm_num) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hY₀ge : Ystar ≤ Y₀ := by
    have : Real.log Ystar ≤ 2 * (L - 1) := by
      have := le_abs_self (Real.log Ystar); linarith
    calc Ystar = Real.exp (Real.log Ystar) := (Real.exp_log hYstar_pos).symm
      _ ≤ Y₀ := Real.exp_le_exp.mpr this
  have hY100 : 100 ≤ Y₀ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hY₀ge
  have hYlog : Real.log (720 * nearRadicalConst S Λ + 1) ≤ Y₀ :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hY₀ge
  have hYε : Real.log ((M + 1) / ε) ≤ Y₀ := le_trans (le_max_right _ _) hY₀ge
  have hY40 : 40 ≤ Y₀ := by linarith
  have hkY : ((0 + 2 : ℕ) : ℝ) + 1 ≤ Y₀ / 10 := by push_cast; linarith
  have hW := nearRadicalEnergy_le_ratio L hΛ hY40 hkY
  rw [← hY₀def, ← hS] at hW
  have hratio := nearRadical_ratio_le (k := 0 + 2) hS0 hΛ0 hkY hY100 hYlog
  have hI : 0 ≤ ∫ u : ℝ, ‖truncatedRiemannKernel L u‖ ^ 2 := integral_nonneg fun _ => by positivity
  have hIM : ∫ u : ℝ, ‖truncatedRiemannKernel L u‖ ^ 2 ≤ M := hM L
  have hexp : Real.exp (-Y₀) * (M + 1) ≤ ε := by
    have h1 : (M + 1) / ε ≤ Real.exp Y₀ := by
      calc (M + 1) / ε = Real.exp (Real.log ((M + 1) / ε)) :=
            (Real.exp_log (div_pos (by linarith) hε)).symm
        _ ≤ Real.exp Y₀ := Real.exp_le_exp.mpr hYε
    rw [div_le_iff₀ hε] at h1
    have h2 : Real.exp (-Y₀) * Real.exp Y₀ = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    have h3 := mul_le_mul_of_nonneg_left h1 (Real.exp_pos (-Y₀)).le
    nlinarith [Real.exp_pos (-Y₀)]
  calc (5 / 4) * S * truncatedRiemannTailEnergy L ^ 2
      ≤ Real.exp (-Y₀) * ∫ u : ℝ, ‖truncatedRiemannKernel L u‖ ^ 2 :=
        hW.trans (mul_le_mul_of_nonneg_right hratio hI)
    _ ≤ Real.exp (-Y₀) * (M + 1) := mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
    _ ≤ ε := hexp

/-! ## The autocorrelation of the polar second difference -/

/-- The autocorrelation `k_L(y) = ∫ Φχ_L(t) Φχ_L(t − y) dt` of the truncated kernel. -/
def truncatedRiemannAutocorr (L y : ℝ) : ℝ :=
  ∫ t, truncatedRiemannKernelReal L t * truncatedRiemannKernelReal L (t - y)

theorem truncatedRiemannAutocorr_nonneg (L y : ℝ) : 0 ≤ truncatedRiemannAutocorr L y :=
  integral_nonneg fun t =>
    mul_nonneg (truncatedRiemannKernelReal_nonneg L t) (truncatedRiemannKernelReal_nonneg L _)

/-- Uniform exponential decay of the truncated autocorrelation. -/
theorem exists_truncatedRiemannAutocorr_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L y : ℝ, truncatedRiemannAutocorr L y ≤ C * Real.exp (-(2 * |y|)) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_riemannPhiKernel_le_exp (B := 4) (by norm_num)
  have hΦ : ∀ x, riemannKernelReal x ≤ C * Real.exp (-(4 * |x|)) := by
    intro x
    have h := hC x
    rwa [riemannPhiKernel_eq_ofReal, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (riemannKernelReal_pos x)] at h
  have hU : ∀ L x, truncatedRiemannKernelReal L x ≤ C * Real.exp (-(4 * |x|)) := by
    intro L x
    unfold truncatedRiemannKernelReal
    calc riemannKernelReal x * bulkCutoff L x ≤ riemannKernelReal x * 1 :=
          mul_le_mul_of_nonneg_left (bulkCutoff_le_one L x) (riemannKernelReal_pos x).le
      _ ≤ _ := by rw [mul_one]; exact hΦ x
  refine ⟨C ^ 2 * ∫ t : ℝ, Real.exp (-|t|),
    mul_nonneg (sq_nonneg _) (integral_nonneg fun _ => (Real.exp_pos _).le), fun L y => ?_⟩
  unfold truncatedRiemannAutocorr
  have hmaj : Integrable fun t : ℝ => C ^ 2 * Real.exp (-(2 * |y|)) * Real.exp (-|t|) :=
    integrable_exp_neg_abs.const_mul _
  calc (∫ t, truncatedRiemannKernelReal L t * truncatedRiemannKernelReal L (t - y))
      ≤ ∫ t : ℝ, C ^ 2 * Real.exp (-(2 * |y|)) * Real.exp (-|t|) := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun t => mul_nonneg
          (truncatedRiemannKernelReal_nonneg L t) (truncatedRiemannKernelReal_nonneg L _)) hmaj
          (Eventually.of_forall fun t => ?_)
        have h1 := hU L t
        have h2 := hU L (t - y)
        have h0 := truncatedRiemannKernelReal_nonneg L t
        have h0' := truncatedRiemannKernelReal_nonneg L (t - y)
        have hexp : Real.exp (-(4 * |t|)) * Real.exp (-(4 * |t - y|)) ≤
            Real.exp (-(2 * |y|)) * Real.exp (-|t|) := by
          rw [← Real.exp_add, ← Real.exp_add]
          apply Real.exp_le_exp.mpr
          have hy : |y| ≤ |t| + |t - y| := by
            rw [abs_le]
            constructor <;>
              linarith [le_abs_self t, neg_abs_le t, le_abs_self (t - y), neg_abs_le (t - y)]
          linarith [abs_nonneg t, abs_nonneg (t - y)]
        calc truncatedRiemannKernelReal L t * truncatedRiemannKernelReal L (t - y)
            ≤ (C * Real.exp (-(4 * |t|))) * (C * Real.exp (-(4 * |t - y|))) :=
              mul_le_mul h1 h2 h0' (by positivity)
          _ = C ^ 2 * (Real.exp (-(4 * |t|)) * Real.exp (-(4 * |t - y|))) := by ring
          _ ≤ C ^ 2 * (Real.exp (-(2 * |y|)) * Real.exp (-|t|)) :=
              mul_le_mul_of_nonneg_left hexp (sq_nonneg _)
          _ = _ := by ring
    _ = C ^ 2 * (∫ t : ℝ, Real.exp (-|t|)) * Real.exp (-(2 * |y|)) := by
        rw [integral_const_mul]; ring

/-- The autocorrelation of a real test, as the corpus weil test. -/
theorem weilTest_ofReal_eq (F : ℝ → ℝ) (y : ℝ) :
    EF.weilTest (fun u => (F u : ℂ)) (fun u => (F u : ℂ)) y = ((∫ t, F t * F (t - y) : ℝ) : ℂ) := by
  unfold EF.weilTest convolution EF.tilde
  rw [← integral_complex_ofReal]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [ContinuousLinearMap.mul_apply', Complex.conj_ofReal]
  rw [show -(y - t) = t - y by ring]
  push_cast
  ring

/-- The autocorrelation of a combination of translates of a compactly supported function. -/
theorem integral_translateComb_autocorr {ι : Type*} (s : Finset ι) (b p : ι → ℝ) {U : ℝ → ℝ}
    (hU : Continuous U) (hUc : HasCompactSupport U) (y : ℝ) :
    ∫ t, (∑ i ∈ s, b i * U (t - p i)) * (∑ j ∈ s, b j * U (t - y - p j)) =
      ∑ i ∈ s, ∑ j ∈ s, b i * b j * ∫ t, U t * U (t - (y + p j - p i)) := by
  have hint : ∀ q r : ℝ, Integrable fun t => U (t - q) * U (t - r) := by
    intro q r
    exact ((hU.comp (continuous_id.sub continuous_const)).mul
      (hU.comp (continuous_id.sub continuous_const))).integrable_of_hasCompactSupport
      ((hUc.comp_homeomorph (Homeomorph.subRight q)).mul_right)
  have e : (fun t => (∑ i ∈ s, b i * U (t - p i)) * (∑ j ∈ s, b j * U (t - y - p j))) =
      fun t => ∑ i ∈ s, ∑ j ∈ s, b i * b j * (U (t - p i) * U (t - (y + p j))) := by
    funext t
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [show t - y - p j = t - (y + p j) by ring]; ring
  rw [e, integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    (hint _ _).const_mul _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => (hint _ _).const_mul _]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul]
  congr 1
  have h := integral_sub_right_eq_self (μ := volume)
    (fun t => U t * U (t - (y + p j - p i))) (p i)
  rw [← h]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  beta_reduce
  rw [show t - p i - (y + p j - p i) = t - (y + p j) by ring]

/-- **Lower bound for the polar autocorrelation.**
`k_f(y) ≥ k(y) − 2α (k(y + c) + k(y − c))`. -/
theorem polarAutocorr_ge (L c y : ℝ) :
    truncatedRiemannAutocorr L y - 2 * polarWeight c *
        (truncatedRiemannAutocorr L (y + c) + truncatedRiemannAutocorr L (y - c)) ≤
      (EF.weilTest (polarRiemannDifference L c) (polarRiemannDifference L c) y).re := by
  have hα := polarWeight_pos c
  rw [polarRiemannDifference_eq, weilTest_ofReal_eq, Complex.ofReal_re]
  have hF : ∀ t, polarRiemannDifferenceReal L c t =
      ∑ i : Fin 3, ![1, -polarWeight c, -polarWeight c] i *
        truncatedRiemannKernelReal L (t - ![0, c, -c] i) := by
    intro t
    simp only [Fin.sum_univ_three, polarRiemannDifferenceReal, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, sub_zero]
    ring
  have e := integral_translateComb_autocorr Finset.univ ![1, -polarWeight c, -polarWeight c]
    ![0, c, -c] (continuous_truncatedRiemannKernelReal L)
    (hasCompactSupport_truncatedRiemannKernelReal L) y
  have hk : ∀ v, (∫ t, truncatedRiemannKernelReal L t * truncatedRiemannKernelReal L (t - v)) =
      truncatedRiemannAutocorr L v := fun v => rfl
  simp only [hk] at e
  have hint : (∫ t, polarRiemannDifferenceReal L c t * polarRiemannDifferenceReal L c (t - y)) =
      ∫ t, (∑ i : Fin 3, ![1, -polarWeight c, -polarWeight c] i *
          truncatedRiemannKernelReal L (t - ![0, c, -c] i)) *
        (∑ j : Fin 3, ![1, -polarWeight c, -polarWeight c] j *
          truncatedRiemannKernelReal L (t - y - ![0, c, -c] j)) := by
    congr 1; funext t; rw [hF, hF (t - y)]
  rw [hint, e]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  have e1 : y + c - 0 = y + c := by ring
  have e2 : y + -c - 0 = y - c := by ring
  have e3 : y + 0 - c = y - c := by ring
  have e4 : y + 0 - -c = y + c := by ring
  have e5 : y + 0 - 0 = y := by ring
  have e6 : y + c - c = y := by ring
  have e7 : y + -c - -c = y := by ring
  have e8 : y + -c - c = y - 2 * c := by ring
  have e9 : y + c - -c = y + 2 * c := by ring
  rw [e1, e2, e3, e4, e5, e6, e7, e8, e9]
  have h1 := truncatedRiemannAutocorr_nonneg L y
  have h2 := truncatedRiemannAutocorr_nonneg L (y - 2 * c)
  have h3 := truncatedRiemannAutocorr_nonneg L (y + 2 * c)
  have h4 : 0 ≤ polarWeight c ^ 2 * (2 * truncatedRiemannAutocorr L y +
      (truncatedRiemannAutocorr L (y - 2 * c) + truncatedRiemannAutocorr L (y + 2 * c))) := by
    positivity
  linarith

/-! ## The excess of a supersystem -/

/-- The excess `Σ_{2 ≤ n ≤ K} (lam(n) − Λ(n))/n` of a Weil-positive supersystem is `o(log K)`. -/
theorem exists_excess_le_log {lam : ℕ → ℝ} (hW : WeilPositive lam)
    (hge : ∀ n, 2 ≤ n → (ArithmeticFunction.vonMangoldt n : ℝ) ≤ lam n) {ε : ℝ} (hε : 0 < ε) :
    ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K →
      ∑ n ∈ Finset.Icc 2 K, (lam n - ArithmeticFunction.vonMangoldt n) / n ≤ ε * Real.log K := by
  obtain ⟨N₀, hN₀⟩ := weil_supersystem_excess_small (lam := lam) hW (ε := ε / 4) (by positivity)
  refine ⟨max N₀ 2, fun K hK => ?_⟩
  have hK2 : 2 ≤ K := le_trans (le_max_right _ _) hK
  have hKN : N₀ ≤ K * K := le_trans (le_trans (le_max_left _ _) hK) (Nat.le_mul_self K)
  have h := hN₀ (K * K) hKN
  set E := ∑ n ∈ Finset.Icc 2 K, (lam n - ArithmeticFunction.vonMangoldt n) / n with hE
  have hw : ∀ n ∈ Finset.Icc 2 K, 0 ≤ (lam n - ArithmeticFunction.vonMangoldt n) / n := by
    intro n hn
    exact div_nonneg (sub_nonneg.mpr (hge n (Finset.mem_Icc.mp hn).1)) (Nat.cast_nonneg _)
  have hE0 : 0 ≤ E := Finset.sum_nonneg hw
  set H := ∑ m ∈ Finset.Icc 1 K, (1 : ℝ) / m with hH
  have hHlog : Real.log K ≤ H := by
    have h1 := log_add_one_le_harmonic K
    rw [harmonic_eq_sum_Icc] at h1
    push_cast at h1
    have h2 : Real.log K ≤ Real.log (K + 1) :=
      Real.log_le_log (by exact_mod_cast (by omega : 0 < K)) (by linarith)
    rw [hH]
    simpa [one_div] using h2.trans h1
  have hsub : E * H ≤ ∑ n ∈ Finset.Icc 2 (K * K), ∑ m ∈ Finset.Icc 1 (K * K),
      (if n * m ≤ K * K then (lam n - ArithmeticFunction.vonMangoldt n) / (n * m) else 0) := by
    rw [hE, hH, Finset.sum_mul_sum]
    have hnn : ∀ n ∈ Finset.Icc 2 (K * K), ∀ m ∈ Finset.Icc 1 (K * K), 0 ≤
        (if n * m ≤ K * K then (lam n - ArithmeticFunction.vonMangoldt n) / (n * m) else 0) := by
      intro n hn m _
      split_ifs
      · exact div_nonneg (sub_nonneg.mpr (hge n (Finset.mem_Icc.mp hn).1)) (by positivity)
      · exact le_rfl
    calc ∑ n ∈ Finset.Icc 2 K, ∑ m ∈ Finset.Icc 1 K,
          (lam n - ArithmeticFunction.vonMangoldt n) / n * (1 / m)
        = ∑ n ∈ Finset.Icc 2 K, ∑ m ∈ Finset.Icc 1 K,
          (if n * m ≤ K * K then (lam n - ArithmeticFunction.vonMangoldt n) / (n * m) else 0) := by
          refine Finset.sum_congr rfl fun n hn => Finset.sum_congr rfl fun m hm => ?_
          have hnK := (Finset.mem_Icc.mp hn).2
          have hmK := (Finset.mem_Icc.mp hm).2
          rw [if_pos (Nat.mul_le_mul hnK hmK)]
          field_simp
      _ ≤ ∑ n ∈ Finset.Icc 2 K, ∑ m ∈ Finset.Icc 1 (K * K),
          (if n * m ≤ K * K then (lam n - ArithmeticFunction.vonMangoldt n) / (n * m) else 0) := by
          refine Finset.sum_le_sum fun n hn => Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.Icc_subset_Icc le_rfl (Nat.le_mul_self K)) fun m hm _ => ?_
          exact hnn n (Finset.Icc_subset_Icc le_rfl (Nat.le_mul_self K) hn) m hm
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.Icc_subset_Icc le_rfl (Nat.le_mul_self K)) fun n hn _ =>
            Finset.sum_nonneg fun m hm => hnn n hn m hm
  have hlogK : 0 < Real.log K := Real.log_pos (by exact_mod_cast (by omega : 1 < K))
  have hlog2 : Real.log ((K * K : ℕ) : ℝ) = 2 * Real.log K := by
    push_cast
    rw [Real.log_mul (by positivity) (by positivity)]; ring
  rw [hlog2] at h
  have h3 : E * Real.log K ≤ ε * Real.log K * Real.log K := by
    calc E * Real.log K ≤ E * H := mul_le_mul_of_nonneg_left hHlog hE0
      _ ≤ ε / 4 * (2 * Real.log K) ^ 2 := hsub.trans h
      _ = ε * Real.log K * Real.log K := by ring
  exact le_of_mul_le_mul_right h3 hlogK

/-- The smoothing `Σ_{2 ≤ n ≤ N} (w(n)/n) e^{−|log n − c|}` of the excess at scale `c`. -/
def excessSmoothing (w : ℕ → ℝ) (N : ℕ) (c : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 2 N, w n / n * Real.exp (-|Real.log n - c|)

theorem continuous_excessSmoothing (w : ℕ → ℝ) (N : ℕ) : Continuous (excessSmoothing w N) := by
  unfold excessSmoothing
  exact continuous_finsetSum _ fun n _ => by fun_prop

theorem excessSmoothing_mono {w : ℕ → ℝ} (hw : ∀ n, 2 ≤ n → 0 ≤ w n) {N N' : ℕ} (hN : N ≤ N')
    (c : ℝ) : excessSmoothing w N c ≤ excessSmoothing w N' c :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc le_rfl hN) fun n hn _ =>
    mul_nonneg (div_nonneg (hw n (Finset.mem_Icc.mp hn).1) (Nat.cast_nonneg _)) (Real.exp_pos _).le

/-- **Averaging over the shift.** Some `c ∈ [M, 2M]` has
`M · Σ (w(n)/n) e^{−|log n − c|} ≤ (∫ e^{−|v|}) Σ w(n)/n`. -/
theorem exists_mul_excessSmoothing_le {w : ℕ → ℝ} (hw : ∀ n, 2 ≤ n → 0 ≤ w n) (N : ℕ) {M : ℝ}
    (hM : 0 < M) :
    ∃ c ∈ Icc M (2 * M), M * excessSmoothing w N c ≤
      (∫ v : ℝ, Real.exp (-|v|)) * ∑ n ∈ Finset.Icc 2 N, w n / n := by
  have hcont := continuous_excessSmoothing w N
  obtain ⟨c, hc, hmin⟩ := (isCompact_Icc (a := M) (b := 2 * M)).exists_isMinOn
    ⟨M, le_rfl, by linarith⟩ hcont.continuousOn
  refine ⟨c, hc, ?_⟩
  have hMM : M ≤ 2 * M := by linarith
  have hlow : ∫ x in M..(2 * M), excessSmoothing w N c ≤ ∫ x in M..(2 * M), excessSmoothing w N x :=
    intervalIntegral.integral_mono_on hMM intervalIntegrable_const (hcont.intervalIntegrable _ _)
      fun x hx => hmin hx
  rw [intervalIntegral.integral_const, smul_eq_mul, show 2 * M - M = M by ring] at hlow
  have hG : Integrable fun v : ℝ => Real.exp (-|v|) := integrable_exp_neg_abs
  have hup : ∫ x in M..(2 * M), excessSmoothing w N x ≤
      (∫ v : ℝ, Real.exp (-|v|)) * ∑ n ∈ Finset.Icc 2 N, w n / n := by
    unfold excessSmoothing
    rw [intervalIntegral.integral_finsetSum fun n _ => by
      exact (Continuous.intervalIntegrable (by fun_prop) _ _), Finset.mul_sum]
    refine Finset.sum_le_sum fun n hn => ?_
    have hwn : 0 ≤ w n / n := div_nonneg (hw n (Finset.mem_Icc.mp hn).1) (Nat.cast_nonneg _)
    rw [intervalIntegral.integral_const_mul, mul_comm (∫ v : ℝ, Real.exp (-|v|))]
    refine mul_le_mul_of_nonneg_left ?_ hwn
    have htr : ∫ x : ℝ, Real.exp (-|Real.log n - x|) = ∫ v : ℝ, Real.exp (-|v|) :=
      integral_sub_left_eq_self (fun v : ℝ => Real.exp (-|v|)) volume (Real.log n)
    rw [← htr, intervalIntegral.integral_of_le hMM]
    refine setIntegral_le_integral ?_ (Eventually.of_forall fun _ => (Real.exp_pos _).le)
    have := hG.comp_sub_left (Real.log n)
    simpa using this
  linarith

/-! ## One atom -/

/-- `α n^{−1/2} e^{−2|log n − c|} ≤ n^{−1} e^{−|log n − c|}`. -/
theorem polarWeight_div_sqrt_mul_exp_le (c : ℝ) {n : ℝ} (hn : 0 < n) :
    polarWeight c / Real.sqrt n * Real.exp (-(2 * |Real.log n - c|)) ≤
      1 / n * Real.exp (-|Real.log n - c|) := by
  set x := Real.log n with hx
  set d := x - c with hd
  set s := Real.sqrt n with hsdef
  have hs : 0 < s := Real.sqrt_pos.mpr hn
  have hsn : s * s = n := Real.mul_self_sqrt hn.le
  have hse : s = Real.exp (x / 2) := by
    have h : Real.exp (x / 2) * Real.exp (x / 2) = n := by
      rw [← Real.exp_add, add_halves, hx, Real.exp_log hn]
    exact (mul_self_inj hs.le (Real.exp_pos _).le).mp (hsn.trans h.symm)
  have hα := polarWeight_pos c
  have hαe : polarWeight c ≤ Real.exp (-(c / 2)) := by
    have h := polarWeight_mul_exp_le c
    have hE : Real.exp (c / 2) * Real.exp (-(c / 2)) = 1 := by
      rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos (c / 2), Real.exp_pos (-(c / 2))]
  have hαs : polarWeight c * s ≤ Real.exp |d| := by
    calc polarWeight c * s ≤ Real.exp (-(c / 2)) * Real.exp (x / 2) := by
          rw [hse]; exact mul_le_mul_of_nonneg_right hαe (Real.exp_pos _).le
      _ = Real.exp (d / 2) := by rw [← Real.exp_add, hd]; ring_nf
      _ ≤ Real.exp |d| := Real.exp_le_exp.mpr (by linarith [le_abs_self d, abs_nonneg d])
  have hkey : polarWeight c * s * Real.exp (-(2 * |d|)) ≤ Real.exp (-|d|) := by
    calc polarWeight c * s * Real.exp (-(2 * |d|)) ≤ Real.exp |d| * Real.exp (-(2 * |d|)) :=
          mul_le_mul_of_nonneg_right hαs (Real.exp_pos _).le
      _ = Real.exp (-|d|) := by rw [← Real.exp_add]; ring_nf
  rw [← hsn]
  calc polarWeight c / s * Real.exp (-(2 * |d|))
      = polarWeight c * s * Real.exp (-(2 * |d|)) / (s * s) := by field_simp
    _ ≤ Real.exp (-|d|) / (s * s) := div_le_div_of_nonneg_right hkey (by positivity)
    _ = 1 / (s * s) * Real.exp (-|d|) := by ring

/-- **One atom.** For `n ≥ 1`, `c ≥ 0` and a nonnegative weight `v`,
`v n^{−1/2} (k_f(log n) + k_f(−log n)) ≥ v n^{−1/2} k(log n) − 8C (v/n) e^{−|log n − c|}`. -/
theorem polarAtom_ge (L : ℝ) {c : ℝ} (hc : 0 ≤ c) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ L y : ℝ, truncatedRiemannAutocorr L y ≤ C * Real.exp (-(2 * |y|))) {n : ℕ}
    (hn : 1 ≤ n) {v : ℝ} (hv : 0 ≤ v) :
    v / Real.sqrt n * truncatedRiemannAutocorr L (Real.log n) -
        8 * C * (v / n * Real.exp (-|Real.log n - c|)) ≤
      v / Real.sqrt n * (EF.weilTest (polarRiemannDifference L c) (polarRiemannDifference L c)
        (Real.log n) + EF.weilTest (polarRiemannDifference L c) (polarRiemannDifference L c)
          (-Real.log n)).re := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  set x := Real.log n with hx
  have hx0 : 0 ≤ x := Real.log_nonneg hnR
  have hsqn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnpos
  have hα := polarWeight_pos c
  have g1 := polarAutocorr_ge L c x
  have g2 := polarAutocorr_ge L c (-x)
  have k1 := hC L (x + c)
  have k2 := hC L (x - c)
  have k3 := hC L (-x + c)
  have k4 := hC L (-x - c)
  have kx := truncatedRiemannAutocorr_nonneg L (-x)
  have habs1 : |x - c| ≤ |x + c| := by
    rw [abs_of_nonneg (by linarith : 0 ≤ x + c)]
    rw [abs_le]; constructor <;> linarith
  have e3 : |-x + c| = |x - c| := by rw [show -x + c = -(x - c) by ring, abs_neg]
  have e4 : |-x - c| = |x + c| := by rw [show -x - c = -(x + c) by ring, abs_neg]
  rw [e3] at k3
  rw [e4] at k4
  have hexp1 : Real.exp (-(2 * |x + c|)) ≤ Real.exp (-(2 * |x - c|)) :=
    Real.exp_le_exp.mpr (by linarith)
  have hfour : truncatedRiemannAutocorr L (x + c) + truncatedRiemannAutocorr L (x - c) +
      (truncatedRiemannAutocorr L (-x + c) + truncatedRiemannAutocorr L (-x - c)) ≤
      4 * (C * Real.exp (-(2 * |x - c|))) := by
    have := mul_le_mul_of_nonneg_left hexp1 hC0
    linarith
  have hmul : 2 * polarWeight c * (truncatedRiemannAutocorr L (x + c) +
      truncatedRiemannAutocorr L (x - c)) + 2 * polarWeight c *
      (truncatedRiemannAutocorr L (-x + c) + truncatedRiemannAutocorr L (-x - c)) ≤
      8 * polarWeight c * (C * Real.exp (-(2 * |x - c|))) := by
    have := mul_le_mul_of_nonneg_left hfour (by positivity : (0 : ℝ) ≤ 2 * polarWeight c)
    linarith
  have hsum : truncatedRiemannAutocorr L x -
      8 * polarWeight c * (C * Real.exp (-(2 * |x - c|))) ≤
      (EF.weilTest (polarRiemannDifference L c) (polarRiemannDifference L c) x +
        EF.weilTest (polarRiemannDifference L c) (polarRiemannDifference L c) (-x)).re := by
    rw [Complex.add_re]
    linarith
  have hweight := polarWeight_div_sqrt_mul_exp_le c hnpos
  rw [← hx] at hweight
  have hmain := mul_le_mul_of_nonneg_left hsum (div_nonneg hv hsqn.le)
  have hw' : v / Real.sqrt n * (8 * polarWeight c * (C * Real.exp (-(2 * |x - c|)))) ≤
      8 * C * (v / n * Real.exp (-|x - c|)) := by
    have := mul_le_mul_of_nonneg_left hweight
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) hC0) hv)
    calc v / Real.sqrt n * (8 * polarWeight c * (C * Real.exp (-(2 * |x - c|))))
        = 8 * C * v * (polarWeight c / Real.sqrt n * Real.exp (-(2 * |x - c|))) := by ring
      _ ≤ 8 * C * v * (1 / n * Real.exp (-|x - c|)) := this
      _ = 8 * C * (v / n * Real.exp (-|x - c|)) := by ring
  have hdist : v / Real.sqrt n * (truncatedRiemannAutocorr L x -
      8 * polarWeight c * (C * Real.exp (-(2 * |x - c|)))) =
      v / Real.sqrt n * truncatedRiemannAutocorr L x -
        v / Real.sqrt n * (8 * polarWeight c * (C * Real.exp (-(2 * |x - c|)))) := by ring
  linarith

/-! ## The theorem -/

/-- **No Weil-positive weight system majorizes `Λ`.** If `lam` is Weil-positive (polar tests,
every level) and `lam(n) ≥ Λ(n)` for all `n ≥ 2`, then `lam(n) = Λ(n)` for all `n ≥ 2`.
Unconditional. -/
theorem eq_vonMangoldt_of_weilPositive_of_ge {lam : ℕ → ℝ} (hW : WeilPositive lam)
    (hge : ∀ n, 2 ≤ n → (ArithmeticFunction.vonMangoldt n : ℝ) ≤ lam n) :
    ∀ n, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n := by
  by_contra hne
  push Not at hne
  obtain ⟨n₀, hn₀, hne₀⟩ := hne
  set w : ℕ → ℝ := fun n => lam n - ArithmeticFunction.vonMangoldt n with hwdef
  have hw : ∀ n, 2 ≤ n → 0 ≤ w n := fun n hn => sub_nonneg.mpr (hge n hn)
  have hw₀ : 0 < w n₀ := lt_of_le_of_ne (hw n₀ hn₀) (sub_ne_zero.mpr hne₀).symm
  have hn₀R : (1 : ℝ) < n₀ := by exact_mod_cast (show 1 < n₀ by omega)
  have hlog₀ : 0 < Real.log n₀ := Real.log_pos hn₀R
  have hsq₀ : 0 < Real.sqrt n₀ := Real.sqrt_pos.mpr (by linarith)
  -- the atom at `n₀`
  obtain ⟨c₀, hc₀, hc₀L⟩ := exists_weilTest_truncatedRiemannKernel_ge hlog₀
  set δ₀ := w n₀ / Real.sqrt n₀ * c₀ with hδ₀
  have hδ₀pos : 0 < δ₀ := by positivity
  -- the decay constant and the smoothing mass
  obtain ⟨CK, hCK0, hCK⟩ := exists_truncatedRiemannAutocorr_le
  set G := ∫ v : ℝ, Real.exp (-|v|) with hG
  have hG0 : 0 ≤ G := integral_nonneg fun _ => (Real.exp_pos _).le
  -- the truncation
  obtain ⟨L₁, hL₁⟩ := exists_nearRadicalEnergy_le (ε := δ₀ / 36) (by positivity)
  set L := max L₁ (Real.log n₀ + 1) with hL
  have hLn : Real.log n₀ + 1 ≤ L := le_max_right _ _
  have hL0 : 0 < L := by linarith
  have hEL := hL₁ L (le_max_left _ _)
  -- the shift
  set ε' := δ₀ / (96 * (CK * G) + 96) with hε'
  have hε'pos : 0 < ε' := by positivity
  obtain ⟨K₀, hK₀⟩ := exists_excess_le_log hW hge hε'pos
  set M : ℝ := max (max L 1) K₀ with hM
  have hM1 : 1 ≤ M := le_trans (le_max_right _ _) (le_max_left _ _)
  have hML : L ≤ M := le_trans (le_max_left _ _) (le_max_left _ _)
  have hMK : (K₀ : ℝ) ≤ M := le_max_right _ _
  have hMpos : 0 < M := by linarith
  set N' := ⌊Real.exp (2 * (L + 2 * M))⌋₊ with hN'
  obtain ⟨c, hcI, hcS⟩ := exists_mul_excessSmoothing_le hw N' hMpos
  have hc0 : 0 ≤ c := by linarith [hcI.1]
  -- the excess bound at `N'`
  have hN'K : K₀ ≤ N' := by
    have h1 : (K₀ : ℝ) ≤ Real.exp (2 * (L + 2 * M)) := by
      have := Real.add_one_le_exp (2 * (L + 2 * M)); linarith
    exact Nat.le_floor h1
  have hEN := hK₀ N' hN'K
  have hlogN' : Real.log N' ≤ 2 * (L + 2 * M) := by
    rcases Nat.eq_zero_or_pos N' with h0 | hpos
    · rw [h0, Nat.cast_zero, Real.log_zero]; linarith
    · calc Real.log N' ≤ Real.log (Real.exp (2 * (L + 2 * M))) :=
            Real.log_le_log (by exact_mod_cast hpos) (Nat.floor_le (Real.exp_pos _).le)
        _ = 2 * (L + 2 * M) := Real.log_exp _
  have hEsum0 : 0 ≤ ∑ n ∈ Finset.Icc 2 N', w n / n := Finset.sum_nonneg fun n hn =>
    div_nonneg (hw n (Finset.mem_Icc.mp hn).1) (Nat.cast_nonneg _)
  have hSmall : excessSmoothing w N' c ≤ 6 * G * ε' := by
    have h1 : M * excessSmoothing w N' c ≤ G * (ε' * (2 * (L + 2 * M))) := by
      refine hcS.trans (mul_le_mul_of_nonneg_left ?_ hG0)
      exact hEN.trans (mul_le_mul_of_nonneg_left hlogN' hε'pos.le)
    have h2 : G * (ε' * (2 * (L + 2 * M))) ≤ M * (6 * G * ε') := by
      have : 2 * (L + 2 * M) ≤ 6 * M := by linarith
      nlinarith [mul_nonneg hG0 hε'pos.le]
    exact le_of_mul_le_mul_left (h1.trans h2) hMpos
  -- the test
  set a := L + c with ha
  have ha0 : 0 ≤ a := by linarith
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = ⌊Real.exp (2 * a)⌋₊ := ⟨_, rfl⟩
  have hNN' : N ≤ N' := hN ▸ Nat.floor_le_floor (Real.exp_le_exp.mpr (by linarith [hcI.2]))
  have hfd : ContDiff ℝ 2 (polarRiemannDifference L c) := contDiff_polarRiemannDifference L c
  have hfs : tsupport (polarRiemannDifference L c) ⊆ Icc (-a) a := tsupport_polarRiemannDifference hc0
  obtain ⟨hp, hm⟩ := paperFT_polarRiemannDifference_pole L c
  have hpos := hW a ha0 _ hfd hfs hp hm
  rw [integral_weilAtomSymbol_eq_sub hfd hfs lam] at hpos
  have hWf := zeta_W_eq_integral_weilAtomSymbol_vonMangoldt hfd hfs hp hm
  rw [← hN] at hpos hWf
  set f := polarRiemannDifference L c with hf
  have hWre : (∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 *
      weilAtomSymbol (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) N (τ / (2 * π))) =
      2 * π * (zetaZeroConfig.W f f).re := by
    rw [hWf, Complex.ofReal_re]; field_simp
  rw [hWre] at hpos
  have hWnorm : ‖zetaZeroConfig.W f f‖ ≤ δ₀ / 4 := by
    obtain ⟨Λ', -, hΛ'⟩ := GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition
    have h := norm_W_polarRiemannDifference_le L hc0 hΛ'
    linarith
  have hπ : 0 < π := Real.pi_pos
  -- the atom sum is at most the zero side
  set T := ∑ n ∈ Finset.Icc 2 N, (lam n - ArithmeticFunction.vonMangoldt n) / Real.sqrt n *
    (EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n)).re with hT
  have hTle : T ≤ δ₀ / 4 := by
    have h1 : T ≤ (zetaZeroConfig.W f f).re := by
      have h2 : 2 * π * T ≤ 2 * π * (zetaZeroConfig.W f f).re := by linarith
      exact le_of_mul_le_mul_left h2 (by positivity)
    exact h1.trans ((Complex.re_le_norm _).trans hWnorm)
  -- the atom sum is at least the `n₀` term minus the smoothing
  have hterm : ∀ n ∈ Finset.Icc 2 N,
      w n / Real.sqrt n * truncatedRiemannAutocorr L (Real.log n) -
        8 * CK * (w n / n * Real.exp (-|Real.log n - c|)) ≤
      (lam n - ArithmeticFunction.vonMangoldt n) / Real.sqrt n *
        (EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n)).re := fun n hn =>
    polarAtom_ge L hc0 hCK0 hCK (by linarith [(Finset.mem_Icc.mp hn).1])
      (hw n (Finset.mem_Icc.mp hn).1)
  have hsumge : ∑ n ∈ Finset.Icc 2 N, (w n / Real.sqrt n * truncatedRiemannAutocorr L (Real.log n) -
      8 * CK * (w n / n * Real.exp (-|Real.log n - c|))) ≤ T := Finset.sum_le_sum hterm
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at hsumge
  -- the `n₀` atom
  have hn₀N : n₀ ∈ Finset.Icc 2 N := by
    refine Finset.mem_Icc.mpr ⟨hn₀, hN ▸ Nat.le_floor ?_⟩
    calc (n₀ : ℝ) = Real.exp (Real.log n₀) := (Real.exp_log (by linarith)).symm
      _ ≤ Real.exp (2 * a) := Real.exp_le_exp.mpr (by linarith)
  have hatom : δ₀ ≤ ∑ n ∈ Finset.Icc 2 N, w n / Real.sqrt n * truncatedRiemannAutocorr L (Real.log n) := by
    have hk₀ : c₀ ≤ truncatedRiemannAutocorr L (Real.log n₀) := by
      have h := hc₀L L hLn
      rwa [weilTest_truncatedRiemannKernel_eq, Complex.ofReal_re] at h
    have hsingle := Finset.single_le_sum (f := fun n => w n / Real.sqrt n *
      truncatedRiemannAutocorr L (Real.log n)) (fun n hn => mul_nonneg
        (div_nonneg (hw n (Finset.mem_Icc.mp hn).1) (Real.sqrt_nonneg _))
        (truncatedRiemannAutocorr_nonneg L _)) hn₀N
    exact le_trans (mul_le_mul_of_nonneg_left hk₀ (by positivity)) hsingle
  have hsm : excessSmoothing w N c ≤ excessSmoothing w N' c := excessSmoothing_mono hw hNN' c
  have hsmN : ∑ n ∈ Finset.Icc 2 N, w n / n * Real.exp (-|Real.log n - c|) =
      excessSmoothing w N c := rfl
  rw [hsmN] at hsumge
  have hbad : 8 * CK * (6 * G * ε') ≤ δ₀ / 2 := by
    have h1 : 8 * CK * (6 * G * ε') = 48 * (CK * G) * ε' := by ring
    rw [h1, hε']
    rw [mul_div_assoc']
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [mul_nonneg hCK0 hG0]
  have := mul_le_mul_of_nonneg_left (hsm.trans hSmall) (by positivity : (0 : ℝ) ≤ 8 * CK)
  linarith

/-! ## RH as the existence of a Weil-positive majorant -/

theorem weilAtomSymbol_congr {lam lam' : ℕ → ℝ} (h : ∀ n, 2 ≤ n → lam n = lam' n) (N : ℕ) (ξ : ℝ) :
    weilAtomSymbol lam N ξ = weilAtomSymbol lam' N ξ := by
  unfold weilAtomSymbol
  congr 1
  exact Finset.sum_congr rfl fun n hn => by rw [h n (Finset.mem_Icc.mp hn).1]

theorem weilPositive_congr {lam lam' : ℕ → ℝ} (h : ∀ n, 2 ≤ n → lam n = lam' n)
    (hW : WeilPositive lam) : WeilPositive lam' := by
  intro a ha f hf hfs hp hm
  have := hW a ha f hf hfs hp hm
  simpa only [weilAtomSymbol_congr h] using this

/-- Weil positivity of `Λ` is the level-wise Hodge index of `ζ`. -/
theorem hodgeIndexAtLevel_of_weilPositive_vonMangoldt
    (hW : WeilPositive fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) (a : ℝ) :
    HodgeIndexAtLevel zetaZeroConfig a := by
  intro f hf hfs hp hm
  set b := max a 0 with hb
  have hfs' : tsupport f ⊆ Icc (-b) b := by
    rcases le_or_gt 0 a with ha | ha
    · rwa [hb, max_eq_left ha]
    · intro x hx
      have := hfs hx
      rw [mem_Icc] at this
      exact absurd (this.1.trans this.2) (by linarith)
  have h := hW b (le_max_right _ _) f hf hfs' hp hm
  have hWf := zeta_W_eq_integral_weilAtomSymbol_vonMangoldt hf hfs' hp hm
  rw [hWf, Complex.ofReal_re]
  exact mul_nonneg (by positivity) h

/-- **Weil's criterion in the corpus's polar form.** RH holds iff the von Mangoldt weights are
Weil-positive. -/
theorem riemannHypothesis_iff_weilPositive_vonMangoldt :
    RiemannHypothesis ↔ WeilPositive fun n => (ArithmeticFunction.vonMangoldt n : ℝ) := by
  constructor
  · intro hRH a ha f hf hfs hp hm
    have hodge := hodgeIndexAtLevel_of_forall_re_eq_half
      (fun ρ hρ => Zeta23.RH_implies_on_line hRH hρ) a f hf hfs hp hm
    have hWf := zeta_W_eq_integral_weilAtomSymbol_vonMangoldt hf hfs hp hm
    rw [hWf, Complex.ofReal_re] at hodge
    have hπ : 0 < 1 / (2 * π) := by positivity
    exact nonneg_of_mul_nonneg_right (by linarith) hπ
  · intro hW
    have hodge := hodgeIndexAtLevel_of_weilPositive_vonMangoldt hW
    rw [rh_iff_xi_ne_zero_right]
    intro s hs h0
    have hs' : 1 / 2 < s.re := hs
    have hs1 : s ≠ 1 := by
      rintro rfl
      rw [xi_one] at h0
      norm_num at h0
    have hζ := (xi_eq_zero_iff (by linarith) hs1).mp h0
    have hlt : s.re < 1 := by
      by_contra hge
      exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp hge) hζ
    have hmem : s ∈ zetaZeroConfig.carrier := (⟨hζ, by linarith, hlt⟩ : IsNontrivialZero s)
    have hγ : 1 ≤ |s.im| := by
      by_contra hγ
      exact riemannZeta_ne_zero_of_abs_im_lt_four (by linarith) hlt (by linarith) hζ
    have := zeta_re_eq_half_of_hodgeIndex hodge hmem hγ
    linarith

/-- **RH is the existence of a Weil-positive majorant of `Λ`.** A Weil-positive `lam ≥ Λ` exists
iff RH holds, and then `lam = Λ` on `n ≥ 2`. -/
theorem riemannHypothesis_iff_exists_weilPositive_ge :
    RiemannHypothesis ↔ ∃ lam : ℕ → ℝ, WeilPositive lam ∧
      ∀ n, 2 ≤ n → (ArithmeticFunction.vonMangoldt n : ℝ) ≤ lam n := by
  constructor
  · intro hRH
    exact ⟨_, riemannHypothesis_iff_weilPositive_vonMangoldt.mp hRH, fun _ _ => le_rfl⟩
  · rintro ⟨lam, hW, hge⟩
    exact riemannHypothesis_iff_weilPositive_vonMangoldt.mpr
      (weilPositive_congr (eq_vonMangoldt_of_weilPositive_of_ge hW hge) hW)

end

end RHTower
