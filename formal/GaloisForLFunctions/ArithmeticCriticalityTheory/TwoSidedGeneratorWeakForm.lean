import GaloisForLFunctions.ArithmeticCriticalityTheory.SignedCombinationOriginFailure
import GaloisForLFunctions.ArithmeticCriticalityTheory.ShiftedGroundStateKernelBounds

/-!
# The Markov energy is the weak form of the two-sided generator

For a Doob test `z ∈ C²_c(ℝ)` (test coordinate `Φ z`) the Markov energy is the pairing of `z` with
its own two-sided generator minus the potential:

    markovEnergy(Φ z) = ∫_ℝ z(x) [ (𝓛_D z)(x) − Φ(x) cosh(x/2) z(x) ] dx,

    (𝓛_D z)(x) = ∫ dm(t) Φ(x) [Φ(x+t)(z(x) − z(x+t)) + Φ(x−t)(z(x) − z(x−t))].

Shift by shift this is summation by parts: `(z(x) − z(x+t))² = z(x)(z(x) − z(x+t)) +
z(x+t)(z(x+t) − z(x))`, and the translation `x ↦ x − t` turns the second piece into the backward
half of the generator. The archimedean shifts are exchanged with the `x`-integral by Fubini
(`|𝓛_D^t z| ≤ 2Φ(0)² Lip(z) t` against `∫ ω(t) t dt < ∞`), the prime shifts by summability of the
integrated atoms (`Φ(x ± log n) ≤ Φ(0)/Φ(R) · Φ(log n − R)` on the support `|x| ≤ R`).

This is the generator calculus of the theory: every ground-state representation is this identity
applied to a factorised test `z = ω u`, and the source equations enter only through `𝓛_D`.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar

noncomputable section

namespace GaloisForLFunctions.ArithmeticCriticalityTheory

/-- The archimedean part of the two-sided generator, `∫_{t>0} ω(t) 𝓛_D^t z(x) dt`. -/
def archTwoSidedGenerator (z : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), archLevyDensity t * twoSidedShiftGenerator z t x

/-- The prime part of the two-sided generator, `Σ_n Λ(n) n^{−1/2} 𝓛_D^{log n} z(x)`. -/
def primeTwoSidedGenerator (z : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑' n : ℕ, vonMangoldtAtom n * twoSidedShiftGenerator z (Real.log n) x

theorem twoSidedGenerator_eq_arch_add_prime (z : ℝ → ℝ) (x : ℝ) :
    twoSidedGenerator z x = archTwoSidedGenerator z x + primeTwoSidedGenerator z x := rfl

theorem continuous_twoSidedShiftGenerator_uncurry {z : ℝ → ℝ} (hz : Continuous z) :
    Continuous fun p : ℝ × ℝ => twoSidedShiftGenerator z p.1 p.2 := by
  have hΦ := continuous_riemannKernelReal
  unfold twoSidedShiftGenerator
  exact (hΦ.comp continuous_snd).mul
    (((hΦ.comp (continuous_snd.add continuous_fst)).mul
      ((hz.comp continuous_snd).sub (hz.comp (continuous_snd.add continuous_fst)))).add
    ((hΦ.comp (continuous_snd.sub continuous_fst)).mul
      ((hz.comp continuous_snd).sub (hz.comp (continuous_snd.sub continuous_fst)))))

theorem continuous_twoSidedShiftGenerator {z : ℝ → ℝ} (hz : Continuous z) (t : ℝ) :
    Continuous fun x => twoSidedShiftGenerator z t x :=
  (continuous_twoSidedShiftGenerator_uncurry hz).comp (continuous_const.prodMk continuous_id)

/-! ### One shift: summation by parts -/

/-- **Summation by parts for one shift.**
`∫ Φ(x)Φ(x+t)(z(x) − z(x+t))² dx = ∫ z(x) 𝓛_D^t z(x) dx`. -/
theorem integral_phiDoobArchShiftJump_eq_integral_mul_twoSidedShiftGenerator {z : ℝ → ℝ}
    (hz : Continuous z) (hzc : HasCompactSupport z) (t : ℝ) :
    (∫ x, phiDoobArchShiftJump z t x) = ∫ x, z x * twoSidedShiftGenerator z t x := by
  have hΦ := continuous_riemannKernelReal
  set f : ℝ → ℝ := fun x =>
    riemannKernelReal x * riemannKernelReal (x + t) * z x * (z x - z (x + t)) with hf_def
  set g : ℝ → ℝ := fun y =>
    riemannKernelReal (y - t) * riemannKernelReal y * z y * (z y - z (y - t)) with hg_def
  have hf : Integrable f := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact ((hΦ.mul (hΦ.comp (continuous_id.add continuous_const))).mul hz).mul
        (hz.sub (hz.comp (continuous_id.add continuous_const)))
    · exact hzc.mul_left.mul_right
  have hg : Integrable g := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact (((hΦ.comp (continuous_id.sub continuous_const)).mul hΦ).mul hz).mul
        (hz.sub (hz.comp (continuous_id.sub continuous_const)))
    · exact hzc.mul_left.mul_right
  have hgt : Integrable fun x => g (x + t) := hg.comp_add_right t
  have h1 : (∫ x, phiDoobArchShiftJump z t x) = ∫ x, (f x + g (x + t)) := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [phiDoobArchShiftJump, hf_def, hg_def, add_sub_cancel_right]
    ring
  have h2 : (∫ x, z x * twoSidedShiftGenerator z t x) = ∫ x, (f x + g x) := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [twoSidedShiftGenerator, hf_def, hg_def]
    ring
  rw [h1, h2, integral_add hf hgt, integral_add hf hg, integral_add_right_eq_self g t]

/-! ### Bounds on one shift of the generator -/

/-- Lipschitz bound: `|𝓛_D^t z(x)| ≤ 2Φ(0)² Λ t` for `t ≥ 0`. -/
theorem abs_twoSidedShiftGenerator_le_lipschitz {z : ℝ → ℝ} {Λ : ℝ}
    (hΛ : ∀ x y, |z y - z x| ≤ Λ * |y - x|) {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    |twoSidedShiftGenerator z t x| ≤ 2 * riemannKernelReal 0 ^ 2 * Λ * t := by
  unfold twoSidedShiftGenerator
  have h0 := riemannKernelReal_pos 0
  have hx := riemannKernelReal_pos x
  have hx' := riemannKernelReal_le_zero_point x
  have hp := riemannKernelReal_pos (x + t)
  have hp' := riemannKernelReal_le_zero_point (x + t)
  have hm := riemannKernelReal_pos (x - t)
  have hm' := riemannKernelReal_le_zero_point (x - t)
  have hd1 : |z x - z (x + t)| ≤ Λ * t := by
    have := hΛ (x + t) x
    rwa [show x - (x + t) = -t by ring, abs_neg, abs_of_nonneg ht] at this
  have hd2 : |z x - z (x - t)| ≤ Λ * t := by
    have := hΛ (x - t) x
    rwa [show x - (x - t) = t by ring, abs_of_nonneg ht] at this
  have hΛ0 : 0 ≤ Λ * t := le_trans (abs_nonneg _) hd1
  rw [abs_mul, abs_of_pos hx]
  have hsum : |riemannKernelReal (x + t) * (z x - z (x + t)) +
      riemannKernelReal (x - t) * (z x - z (x - t))| ≤ 2 * riemannKernelReal 0 * (Λ * t) := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_pos hp, abs_of_pos hm]
    nlinarith [mul_le_mul hp' hd1 (abs_nonneg _) h0.le, mul_le_mul hm' hd2 (abs_nonneg _) h0.le]
  nlinarith [mul_le_mul hx' hsum (abs_nonneg _) h0.le]

/-- Kernel bound: `|𝓛_D^t z(x)| ≤ 2 Z Φ(0) (Φ(x+t) + Φ(x−t))` when `|z| ≤ Z`. -/
theorem abs_twoSidedShiftGenerator_le_kernel {z : ℝ → ℝ} {Z : ℝ} (hZ : ∀ x, |z x| ≤ Z)
    (t x : ℝ) :
    |twoSidedShiftGenerator z t x| ≤
      2 * Z * riemannKernelReal 0 * (riemannKernelReal (x + t) + riemannKernelReal (x - t)) := by
  unfold twoSidedShiftGenerator
  have h0 := riemannKernelReal_pos 0
  have hx := riemannKernelReal_pos x
  have hx' := riemannKernelReal_le_zero_point x
  have hp := riemannKernelReal_pos (x + t)
  have hm := riemannKernelReal_pos (x - t)
  have hd1 : |z x - z (x + t)| ≤ 2 * Z := by
    have := abs_sub (z x) (z (x + t))
    linarith [hZ x, hZ (x + t)]
  have hd2 : |z x - z (x - t)| ≤ 2 * Z := by
    have := abs_sub (z x) (z (x - t))
    linarith [hZ x, hZ (x - t)]
  rw [abs_mul, abs_of_pos hx]
  have hsum : |riemannKernelReal (x + t) * (z x - z (x + t)) +
      riemannKernelReal (x - t) * (z x - z (x - t))| ≤
        2 * Z * (riemannKernelReal (x + t) + riemannKernelReal (x - t)) := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_pos hp, abs_of_pos hm]
    nlinarith [mul_le_mul_of_nonneg_left hd1 hp.le, mul_le_mul_of_nonneg_left hd2 hm.le]
  have hZ0 : 0 ≤ Z := le_trans (abs_nonneg _) (hZ x)
  have hK : 0 ≤ 2 * Z * (riemannKernelReal (x + t) + riemannKernelReal (x - t)) := by positivity
  nlinarith [mul_le_mul hx' hsum (abs_nonneg _) h0.le]

/-- On a support radius `R`, both translates of `Φ` at `log n` are dominated by one summable prime
weight: `Φ(x ± log n) ≤ Φ(0)/Φ(R) · Φ(log n − R)` for `|x| ≤ R`. -/
theorem riemannKernelReal_add_add_sub_le {R x : ℝ} (hx : |x| ≤ R) (n : ℕ) :
    riemannKernelReal (x + Real.log n) + riemannKernelReal (x - Real.log n) ≤
      2 * (riemannKernelReal 0 / riemannKernelReal R) * riemannKernelReal (R - Real.log n) := by
  have hlog := Real.log_natCast_nonneg n
  have e1 : riemannKernelReal (x + Real.log n) = riemannKernelReal (Real.log n - -x) := by
    rw [show Real.log n - -x = x + Real.log n by ring]
  have e2 : riemannKernelReal (x - Real.log n) = riemannKernelReal (Real.log n - x) := by
    rw [show x - Real.log n = -(Real.log n - x) by ring, riemannKernelReal_neg']
  have e3 : riemannKernelReal (R - Real.log n) = riemannKernelReal (Real.log n - R) := by
    rw [show R - Real.log n = -(Real.log n - R) by ring, riemannKernelReal_neg']
  have h1 := riemannKernelReal_sub_le_mul_sub_of_le (a := -x) (b := R) (y := Real.log n)
    (by linarith [neg_abs_le x]) hlog
  have h2 := riemannKernelReal_sub_le_mul_sub_of_le (a := x) (b := R) (y := Real.log n)
    (by linarith [le_abs_self x]) hlog
  rw [e1, e2, e3]
  linarith

/-! ### The archimedean shifts -/

/-- The archimedean integrand `ω(t) z(x) 𝓛_D^t z(x)` is integrable on `(0,∞) × ℝ`. -/
theorem integrable_archLevy_mul_twoSidedShiftGenerator {z : ℝ → ℝ} (hz : ContDiff ℝ 2 z)
    (hzc : HasCompactSupport z) :
    Integrable (Function.uncurry fun t x => archLevyDensity t * (z x * twoSidedShiftGenerator z t x))
      ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
  obtain ⟨Λ, hΛ0, hΛ⟩ := exists_lipschitz_bound_of_compactSupport (hz.of_le (by norm_num)) hzc
  have hzcont := hz.continuous
  have hmaj : Integrable (fun p : ℝ × ℝ =>
      (archLevyDensity p.1 * p.1) * (2 * riemannKernelReal 0 ^ 2 * Λ * |z p.2|))
      ((volume.restrict (Ioi (0 : ℝ))).prod volume) :=
    integrableOn_archLevyDensity_mul_id.mul_prod
      ((hzcont.integrable_of_hasCompactSupport hzc).abs.const_mul _)
  refine hmaj.mono' ?_ ?_
  · exact ((measurable_archLevyDensity.comp measurable_fst).mul
      ((hzcont.comp continuous_snd).mul (continuous_twoSidedShiftGenerator_uncurry hzcont)).measurable)
      |>.aestronglyMeasurable
  · rw [Measure.restrict_prod_eq_prod_univ]
    refine ae_restrict_of_forall_mem (measurableSet_Ioi.prod MeasurableSet.univ) fun p hp => ?_
    have ht : 0 < p.1 := hp.1
    have hb := abs_twoSidedShiftGenerator_le_lipschitz hΛ ht.le p.2
    show ‖archLevyDensity p.1 * (z p.2 * twoSidedShiftGenerator z p.1 p.2)‖ ≤ _
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (archLevyDensity_pos ht), abs_mul]
    have hA := archLevyDensity_pos ht
    have hz0 := abs_nonneg (z p.2)
    nlinarith [mul_le_mul_of_nonneg_left hb (mul_nonneg hA.le hz0)]

/-- **Archimedean weak form.** `E_arch(z) = ∫ z(x) (∫ ω(t) 𝓛_D^t z(x) dt) dx`. -/
theorem phiDoobArchJumpEnergy_eq_integral_mul_archTwoSidedGenerator {z : ℝ → ℝ}
    (hz : ContDiff ℝ 2 z) (hzc : HasCompactSupport z) :
    phiDoobArchJumpEnergy z = ∫ x, z x * archTwoSidedGenerator z x := by
  have hint := integrable_archLevy_mul_twoSidedShiftGenerator hz hzc
  unfold phiDoobArchJumpEnergy archTwoSidedGenerator
  have h1 : (∫ t in Ioi (0 : ℝ), archLevyDensity t * ∫ x : ℝ, phiDoobArchShiftJump z t x) =
      ∫ t in Ioi (0 : ℝ), ∫ x : ℝ, archLevyDensity t * (z x * twoSidedShiftGenerator z t x) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [integral_phiDoobArchShiftJump_eq_integral_mul_twoSidedShiftGenerator hz.continuous hzc,
      integral_const_mul]
  rw [h1, integral_integral_swap hint]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  ring

theorem integrable_mul_archTwoSidedGenerator {z : ℝ → ℝ} (hz : ContDiff ℝ 2 z)
    (hzc : HasCompactSupport z) : Integrable fun x => z x * archTwoSidedGenerator z x := by
  have h := (integrable_archLevy_mul_twoSidedShiftGenerator hz hzc).integral_prod_right
  refine h.congr (Eventually.of_forall fun x => ?_)
  simp only [Function.uncurry_apply_pair, archTwoSidedGenerator]
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  ring

/-! ### The prime shifts -/

/-- On the support radius the integrated prime atoms are dominated by a summable weight. -/
theorem abs_atom_mul_twoSidedShiftGenerator_le {z : ℝ → ℝ} {Z R : ℝ} (hZ : ∀ x, |z x| ≤ Z)
    (hsupp : ∀ x, R < |x| → z x = 0) (n : ℕ) (x : ℝ) :
    |vonMangoldtAtom n * (z x * twoSidedShiftGenerator z (Real.log n) x)| ≤
      (4 * Z * riemannKernelReal 0 * (riemannKernelReal 0 / riemannKernelReal R)) *
        (vonMangoldtAtom n * riemannKernelReal (R - Real.log n)) * |z x| := by
  have hΛ := vonMangoldtAtom_nonneg n
  have hZ0 : 0 ≤ Z := le_trans (abs_nonneg _) (hZ x)
  by_cases hx : |x| ≤ R
  · have hb := abs_twoSidedShiftGenerator_le_kernel hZ (Real.log n) x
    have hk := riemannKernelReal_add_add_sub_le hx n
    have hc : 0 ≤ 2 * Z * riemannKernelReal 0 := by
      have := riemannKernelReal_pos 0
      positivity
    have hG : |twoSidedShiftGenerator z (Real.log n) x| ≤
        2 * Z * riemannKernelReal 0 *
          (2 * (riemannKernelReal 0 / riemannKernelReal R) * riemannKernelReal (R - Real.log n)) :=
      hb.trans (mul_le_mul_of_nonneg_left hk hc)
    rw [abs_mul, abs_of_nonneg hΛ, abs_mul]
    have hz0 := abs_nonneg (z x)
    calc vonMangoldtAtom n * (|z x| * |twoSidedShiftGenerator z (Real.log n) x|)
        ≤ vonMangoldtAtom n * (|z x| * (2 * Z * riemannKernelReal 0 *
          (2 * (riemannKernelReal 0 / riemannKernelReal R) * riemannKernelReal (R - Real.log n)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hG hz0) hΛ
      _ = _ := by ring
  · rw [hsupp x (not_le.mp hx)]
    simp

theorem summable_atom_mul_kernel_sub (R : ℝ) :
    Summable fun n : ℕ => vonMangoldtAtom n * riemannKernelReal (R - Real.log n) :=
  summable_primeShift_left R

/-- **Prime weak form.** `Σ_n ∫ Φ(x)Φ(x+log n)(z(x) − z(x+log n))² Λ(n)n^{−1/2} dx
= ∫ z(x) (Σ_n Λ(n) n^{−1/2} 𝓛_D^{log n} z(x)) dx`. -/
theorem tsum_integral_phiDoobPrimeJump_eq_integral_mul_primeTwoSidedGenerator {z : ℝ → ℝ}
    (hz : ContDiff ℝ 2 z) (hzc : HasCompactSupport z) :
    (∑' n : ℕ, ∫ x : ℝ, phiDoobPrimeJump z n x) = ∫ x, z x * primeTwoSidedGenerator z x := by
  have hzcont := hz.continuous
  obtain ⟨Z, hZ⟩ := hzc.exists_bound_of_continuous hzcont
  have hZ' : ∀ x, |z x| ≤ Z := fun x => by simpa [Real.norm_eq_abs] using hZ x
  obtain ⟨R, -, hsupp⟩ := exists_support_radius hzc
  set F : ℕ → ℝ → ℝ := fun n x => vonMangoldtAtom n * (z x * twoSidedShiftGenerator z (Real.log n) x)
    with hF_def
  have hzi : Integrable fun x => |z x| := (hzcont.integrable_of_hasCompactSupport hzc).abs
  have hFint : ∀ n, Integrable (F n) := fun n => by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact continuous_const.mul (hzcont.mul (continuous_twoSidedShiftGenerator hzcont _))
    · exact (hzc.mul_right).mul_left
  set K := 4 * Z * riemannKernelReal 0 * (riemannKernelReal 0 / riemannKernelReal R)
  have hsum : Summable fun n => ∫ x, ‖F n x‖ := by
    have hmaj : Summable fun n : ℕ =>
        K * (vonMangoldtAtom n * riemannKernelReal (R - Real.log n)) * ∫ x, |z x| :=
      ((summable_atom_mul_kernel_sub R).mul_left K).mul_right _
    refine hmaj.of_nonneg_of_le (fun n => integral_nonneg fun x => norm_nonneg _) fun n => ?_
    rw [← integral_const_mul]
    refine integral_mono (hFint n).norm (hzi.const_mul _) fun x => ?_
    simp only [Real.norm_eq_abs]
    exact abs_atom_mul_twoSidedShiftGenerator_le hZ' hsupp n x
  have h1 : (∑' n : ℕ, ∫ x : ℝ, phiDoobPrimeJump z n x) = ∑' n : ℕ, ∫ x, F n x := by
    refine tsum_congr fun n => ?_
    simp_rw [phiDoobPrimeJump_eq_atom_mul_shiftJump z n]
    rw [integral_const_mul,
      integral_phiDoobArchShiftJump_eq_integral_mul_twoSidedShiftGenerator hzcont hzc,
      ← integral_const_mul]
  rw [h1, integral_tsum_of_summable_integral_norm hFint hsum]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [hF_def, primeTwoSidedGenerator]
  rw [← tsum_mul_left]
  exact tsum_congr fun n => by ring

/-- The prime atoms of the generator are summable at every point. -/
theorem summable_atom_twoSidedShiftGenerator {z : ℝ → ℝ} {Z : ℝ} (hZ : ∀ x, |z x| ≤ Z)
    (x : ℝ) :
    Summable fun n : ℕ => vonMangoldtAtom n * twoSidedShiftGenerator z (Real.log n) x := by
  refine Summable.of_norm_bounded
    ((summable_primeKernelSum x).mul_left (2 * Z * riemannKernelReal 0)) fun n => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (vonMangoldtAtom_nonneg n)]
  have hb := abs_twoSidedShiftGenerator_le_kernel hZ (Real.log n) x
  calc vonMangoldtAtom n * |twoSidedShiftGenerator z (Real.log n) x|
      ≤ vonMangoldtAtom n * (2 * Z * riemannKernelReal 0 *
        (riemannKernelReal (x + Real.log n) + riemannKernelReal (x - Real.log n))) :=
        mul_le_mul_of_nonneg_left hb (vonMangoldtAtom_nonneg n)
    _ = _ := by ring

theorem integrable_mul_primeTwoSidedGenerator {z : ℝ → ℝ} (hz : ContDiff ℝ 2 z)
    (hzc : HasCompactSupport z) : Integrable fun x => z x * primeTwoSidedGenerator z x := by
  have hzcont := hz.continuous
  obtain ⟨Z, hZ⟩ := hzc.exists_bound_of_continuous hzcont
  have hZ' : ∀ x, |z x| ≤ Z := fun x => by simpa [Real.norm_eq_abs] using hZ x
  obtain ⟨R, -, hsupp⟩ := exists_support_radius hzc
  set K := 4 * Z * riemannKernelReal 0 * (riemannKernelReal 0 / riemannKernelReal R)
  set S := ∑' n : ℕ, vonMangoldtAtom n * riemannKernelReal (R - Real.log n)
  have hzi : Integrable fun x => |z x| := (hzcont.integrable_of_hasCompactSupport hzc).abs
  have hmeas : AEStronglyMeasurable (fun x => z x * primeTwoSidedGenerator z x) volume := by
    refine aestronglyMeasurable_of_tendsto_ae (f := fun N x => z x *
      ∑ n ∈ Finset.range N, vonMangoldtAtom n * twoSidedShiftGenerator z (Real.log n) x)
      atTop (fun N => ?_) (Eventually.of_forall fun x => ?_)
    · exact (hzcont.mul (continuous_finsetSum _ fun n _ =>
        continuous_const.mul (continuous_twoSidedShiftGenerator hzcont _))).aestronglyMeasurable
    · exact ((summable_atom_twoSidedShiftGenerator hZ' x).hasSum.tendsto_sum_nat).const_mul _
  refine (hzi.const_mul (K * S)).mono' hmeas (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, primeTwoSidedGenerator, ← tsum_mul_left]
  have hterm := abs_atom_mul_twoSidedShiftGenerator_le hZ' hsupp
  have hB : Summable fun n : ℕ =>
      K * (vonMangoldtAtom n * riemannKernelReal (R - Real.log n)) * |z x| :=
    ((summable_atom_mul_kernel_sub R).mul_left K).mul_right _
  have hnorm : Summable fun n : ℕ =>
      ‖z x * (vonMangoldtAtom n * twoSidedShiftGenerator z (Real.log n) x)‖ :=
    hB.of_nonneg_of_le (fun n => norm_nonneg _) fun n => by
      rw [Real.norm_eq_abs, show z x * (vonMangoldtAtom n * twoSidedShiftGenerator z (Real.log n) x)
        = vonMangoldtAtom n * (z x * twoSidedShiftGenerator z (Real.log n) x) by ring]
      exact hterm n x
  calc |∑' n : ℕ, z x * (vonMangoldtAtom n * twoSidedShiftGenerator z (Real.log n) x)|
      ≤ ∑' n : ℕ, ‖z x * (vonMangoldtAtom n * twoSidedShiftGenerator z (Real.log n) x)‖ := by
        rw [← Real.norm_eq_abs]
        exact norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n : ℕ, K * (vonMangoldtAtom n * riemannKernelReal (R - Real.log n)) * |z x| :=
        Summable.tsum_le_tsum (fun n => by
          rw [Real.norm_eq_abs, show z x * (vonMangoldtAtom n *
            twoSidedShiftGenerator z (Real.log n) x) =
              vonMangoldtAtom n * (z x * twoSidedShiftGenerator z (Real.log n) x) by ring]
          exact hterm n x) hnorm hB
    _ = K * S * |z x| := by
        rw [tsum_mul_right, tsum_mul_left]

/-! ### The weak form -/

/-- **The Markov energy is the weak form of the two-sided generator.** For every `z ∈ C²_c(ℝ)`,
`markovEnergy(Φ z) = ∫ z(x) [(𝓛_D z)(x) − Φ(x) cosh(x/2) z(x)] dx`. -/
theorem markovEnergy_phiDoob_eq_integral_mul_twoSidedGenerator_sub_potential {z : ℝ → ℝ}
    (hz : ContDiff ℝ 2 z) (hzc : HasCompactSupport z) :
    markovEnergy (fun x => (phiDoobTest z x : ℂ)) =
      ∫ x, z x * (twoSidedGenerator z x - riemannKernelReal x * Real.cosh (x / 2) * z x) := by
  have hzcont := hz.continuous
  have hA := integrable_mul_archTwoSidedGenerator hz hzc
  have hP := integrable_mul_primeTwoSidedGenerator hz hzc
  have hC : Integrable fun x => z x * (riemannKernelReal x * Real.cosh (x / 2) * z x) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ hzc.mul_right
    exact hzcont.mul ((continuous_riemannKernelReal.mul
      (Real.continuous_cosh.comp (continuous_id.div_const 2))).mul hzcont)
  rw [phiDoob_markovEnergy_eq_archJump_add_primeJump_sub_coshMass hz hzc,
    phiDoobArchJumpEnergy_eq_integral_mul_archTwoSidedGenerator hz hzc,
    tsum_integral_phiDoobPrimeJump_eq_integral_mul_primeTwoSidedGenerator hz hzc]
  have hcosh : phiDoobCoshMass (fun x => z x ^ 2) =
      ∫ x, z x * (riemannKernelReal x * Real.cosh (x / 2) * z x) := by
    unfold phiDoobCoshMass phiDoobTest
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    ring
  have hsplit : (∫ x, z x * (twoSidedGenerator z x -
      riemannKernelReal x * Real.cosh (x / 2) * z x)) =
      (∫ x, z x * archTwoSidedGenerator z x) + (∫ x, z x * primeTwoSidedGenerator z x) -
        ∫ x, z x * (riemannKernelReal x * Real.cosh (x / 2) * z x) := by
    have hAP : Integrable fun x => z x * archTwoSidedGenerator z x +
        z x * primeTwoSidedGenerator z x := hA.add hP
    have h1 : (∫ x, z x * (twoSidedGenerator z x -
        riemannKernelReal x * Real.cosh (x / 2) * z x)) =
        ∫ x, ((z x * archTwoSidedGenerator z x + z x * primeTwoSidedGenerator z x) -
          z x * (riemannKernelReal x * Real.cosh (x / 2) * z x)) := by
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [twoSidedGenerator_eq_arch_add_prime]
      ring
    rw [h1, integral_sub hAP hC, integral_add hA hP]
  rw [hcosh, hsplit]

end GaloisForLFunctions.ArithmeticCriticalityTheory

end
