import GaloisForLFunctions.ArithmeticCriticalityTheory.GeneralGaugeGroundStateRepresentation

/-!
# Theta convolutions: the continuous span of the translate ground states

For `φ ∈ C²_c(ℝ)` the theta convolution `M_φ = Φ ∗ φ`, `M_φ(x) = ∫ φ(b) Φ(x − b) db`, is the test
coordinate of the gauge `ω_φ = M_φ / Φ = ∫ φ(b) τ_b db`, a continuous superposition of translate
ground states, outside the finite span. Superposing the translate source equations,

    (𝓛_D ω_φ)(x) − Φ(x) cosh(x/2) ω_φ(x) = −Φ(x) ∫ φ(b) cosh((x − b)/2) db
                                           = −Φ(x) (A_φ cosh(x/2) − B_φ sinh(x/2)),

with `A_φ = ∫ φ(b) cosh(b/2) db`, `B_φ = ∫ φ(b) sinh(b/2) db` (`twoSidedGenerator_convGauge_sub_potential`).
The exchange of the superposition with the shift integral is uniform in `b`: the archimedean
integrand of `𝓛_D^t τ_b` is bounded by `4Φ(0)` times the integrable gamma source bound, by the
harmonic identity's regularisation, and the prime atoms are bounded on compact sets of `b`.

Consequently every structural law of the finite span holds for theta convolutions:
`markovEnergy(Φ(ω_φ u_L)) → (B_φ² − A_φ²)/2` (the Lorentz law, `tendsto_markovEnergy_convPlateau`);
the harmonic ones (`A_φ = B_φ = 0`: `φ` orthogonal to `cosh(·/2)` and `sinh(·/2)`) lie in the radical
of the Markov form and carry a potential-free representation `markovEnergy(Φ(ω_φ u)) = J_{Φ∗φ}(u)`
with conductances `(Φ ∗ φ)(x)(Φ ∗ φ)(x + t)`. The plateau-limit energy of the whole convolution
family factors through the two pole coefficients `φ ↦ (A_φ, B_φ)`.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar RHTower.ThetaSourceWard

noncomputable section

namespace GaloisForLFunctions.ArithmeticCriticalityTheory

/-! ### The theta convolution and its gauge -/

/-- The theta convolution `(Φ ∗ φ)(x) = ∫ φ(b) Φ(x − b) db`. -/
def thetaConv (φ : ℝ → ℝ) (x : ℝ) : ℝ := ∫ b, φ b * riemannKernelReal (x - b)

/-- The convolution gauge `ω_φ = (Φ ∗ φ)/Φ`. -/
def convGauge (φ : ℝ → ℝ) (x : ℝ) : ℝ := thetaConv φ x / riemannKernelReal x

theorem thetaConv_eq_convolution (φ : ℝ → ℝ) :
    thetaConv φ = convolution φ riemannKernelReal (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
  funext x
  rw [convolution_def]
  rfl

theorem contDiff_thetaConv {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) :
    ContDiff ℝ 2 (thetaConv φ) := by
  rw [thetaConv_eq_convolution]
  exact hφc.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) (n := 2) hφ
    integrable_riemannKernelReal.locallyIntegrable

theorem riemannKernelReal_mul_convGauge (φ : ℝ → ℝ) (x : ℝ) :
    riemannKernelReal x * convGauge φ x = thetaConv φ x := by
  unfold convGauge
  rw [mul_div_cancel₀ _ (riemannKernelReal_pos x).ne']

theorem contDiff_convGauge {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) :
    ContDiff ℝ 2 (convGauge φ) :=
  (contDiff_thetaConv hφ hφc).div contDiff_riemannKernelReal fun x => (riemannKernelReal_pos x).ne'

theorem integrable_mul_riemannKernelReal_sub {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) (y : ℝ) : Integrable fun b => φ b * riemannKernelReal (y - b) :=
  (hφ.mul (continuous_riemannKernelReal.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
    hφc.mul_right

/-- The shift generator of the convolution gauge is the superposition of those of the translates. -/
theorem twoSidedShiftGenerator_convGauge {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) (t x : ℝ) :
    twoSidedShiftGenerator (convGauge φ) t x =
      ∫ b, φ b * twoSidedShiftGenerator (translateGroundState b) t x := by
  have hM : ∀ y, riemannKernelReal y * convGauge φ y = thetaConv φ y :=
    riemannKernelReal_mul_convGauge φ
  have e1 : twoSidedShiftGenerator (convGauge φ) t x =
      thetaConv φ x * (riemannKernelReal (x + t) + riemannKernelReal (x - t)) -
        riemannKernelReal x * (thetaConv φ (x + t) + thetaConv φ (x - t)) := by
    unfold twoSidedShiftGenerator
    linear_combination (riemannKernelReal (x + t) + riemannKernelReal (x - t)) * hM x -
      riemannKernelReal x * hM (x + t) - riemannKernelReal x * hM (x - t)
  have i0 := integrable_mul_riemannKernelReal_sub hφ hφc x
  have i1 := integrable_mul_riemannKernelReal_sub hφ hφc (x + t)
  have i2 := integrable_mul_riemannKernelReal_sub hφ hφc (x - t)
  rw [e1]
  unfold thetaConv
  have i12 : Integrable fun b => φ b * riemannKernelReal (x + t - b) +
      φ b * riemannKernelReal (x - t - b) := i1.add i2
  rw [← integral_add i1 i2, ← integral_mul_const, ← integral_const_mul,
    ← integral_sub (i0.mul_const _) (i12.const_mul _)]
  refine integral_congr_ae (Eventually.of_forall fun b => ?_)
  simp only
  rw [twoSidedShiftGenerator_translateGroundState,
    show x + t - b = x - b + t by ring, show x - t - b = x - b - t by ring]
  ring

/-! ### Uniform bounds on the translate generators -/

theorem abs_symArchTerm_le_two_mul_gammaSourceBound (y : ℝ) {u : ℝ} (hu : 0 < u) :
    |symArchTerm y u| ≤ 2 * gammaSourceBound u := by
  rw [symArchTerm_eq_add_gammaSourceTerm]
  have h1 := abs_gammaSourceTerm_le_bound y hu
  have h2 := abs_gammaSourceTerm_le_bound (-y) hu
  linarith [abs_add_le (gammaSourceTerm y u) (gammaSourceTerm (-y) u)]

/-- Uniformly in the translate: `|ω(u) 𝓛_D^u τ_b(x)| ≤ 4 Φ(0) gammaSourceBound(u)`. -/
theorem abs_archLevy_mul_twoSidedShiftGenerator_translateGroundState_le (b x : ℝ) {u : ℝ}
    (hu : 0 < u) :
    |archLevyDensity u * twoSidedShiftGenerator (translateGroundState b) u x| ≤
      4 * riemannKernelReal 0 * gammaSourceBound u := by
  rw [archLevy_twoSidedShiftGenerator_translateGroundState, abs_neg]
  have h1 := abs_symArchTerm_le_two_mul_gammaSourceBound x hu
  have h2 := abs_symArchTerm_le_two_mul_gammaSourceBound (x - b) hu
  have p1 := riemannKernelReal_pos (x - b)
  have p2 := riemannKernelReal_pos x
  have q1 := riemannKernelReal_le_zero_point (x - b)
  have q2 := riemannKernelReal_le_zero_point x
  have hg : 0 ≤ gammaSourceBound u := le_trans (abs_nonneg _) (abs_gammaSourceTerm_le_bound x hu)
  refine (abs_sub _ _).trans ?_
  rw [abs_mul, abs_mul, abs_of_pos p1, abs_of_pos p2]
  nlinarith [mul_le_mul q1 h1 (abs_nonneg _) (riemannKernelReal_pos 0).le,
    mul_le_mul q2 h2 (abs_nonneg _) (riemannKernelReal_pos 0).le]

/-- The prime atoms of `𝓛_D τ_b` are dominated by a summable weight, uniformly for `|b| ≤ R'`. -/
theorem abs_atom_twoSidedShiftGenerator_translateGroundState_le {R' x b : ℝ} (hb : |b| ≤ R')
    (n : ℕ) :
    |vonMangoldtAtom n * twoSidedShiftGenerator (translateGroundState b) (Real.log n) x| ≤
      4 * riemannKernelReal 0 * (riemannKernelReal 0 / riemannKernelReal (|x| + R')) *
        (vonMangoldtAtom n * riemannKernelReal (|x| + R' - Real.log n)) := by
  rw [atom_twoSidedShiftGenerator_translateGroundState]
  have hΛ := vonMangoldtAtom_nonneg n
  have k1 := riemannKernelReal_add_add_sub_le (R := |x| + R') (x := x)
    (by linarith [abs_nonneg b, abs_nonneg x]) n
  have k2 := riemannKernelReal_add_add_sub_le (R := |x| + R') (x := x - b)
    (by linarith [abs_sub x b]) n
  have p1 := riemannKernelReal_pos (x - b)
  have p2 := riemannKernelReal_pos x
  have q1 := riemannKernelReal_le_zero_point (x - b)
  have q2 := riemannKernelReal_le_zero_point x
  have s1 : 0 ≤ riemannKernelReal (x + Real.log n) + riemannKernelReal (x - Real.log n) := by
    have := riemannKernelReal_pos (x + Real.log n)
    have := riemannKernelReal_pos (x - Real.log n)
    linarith
  have s2 : 0 ≤ riemannKernelReal (x - b + Real.log n) + riemannKernelReal (x - b - Real.log n) := by
    have := riemannKernelReal_pos (x - b + Real.log n)
    have := riemannKernelReal_pos (x - b - Real.log n)
    linarith
  set W := 2 * (riemannKernelReal 0 / riemannKernelReal (|x| + R')) *
    riemannKernelReal (|x| + R' - Real.log n)
  have hW0 : 0 ≤ W := by
    have := riemannKernelReal_pos 0
    have := riemannKernelReal_pos (|x| + R')
    have := riemannKernelReal_pos (|x| + R' - Real.log n)
    positivity
  refine (abs_sub _ _).trans ?_
  rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_pos p1, abs_of_pos p2, abs_of_nonneg hΛ,
    abs_of_nonneg s1, abs_of_nonneg s2]
  have hW : 4 * riemannKernelReal 0 * (riemannKernelReal 0 / riemannKernelReal (|x| + R')) *
      (vonMangoldtAtom n * riemannKernelReal (|x| + R' - Real.log n)) =
      riemannKernelReal 0 * (vonMangoldtAtom n * W) + riemannKernelReal 0 * (vonMangoldtAtom n * W) := by
    ring
  rw [hW]
  refine add_le_add ?_ ?_
  · exact mul_le_mul q1 (mul_le_mul_of_nonneg_left k1 hΛ) (by positivity) (riemannKernelReal_pos 0).le
  · exact mul_le_mul q2 (mul_le_mul_of_nonneg_left k2 hΛ) (by positivity) (riemannKernelReal_pos 0).le

/-! ### Superposing the generator -/

theorem continuous_twoSidedShiftGenerator_translate_uncurry (x : ℝ) :
    Continuous fun p : ℝ × ℝ => twoSidedShiftGenerator (translateGroundState p.2) p.1 x := by
  have hΦ := continuous_riemannKernelReal
  have e : (fun p : ℝ × ℝ => twoSidedShiftGenerator (translateGroundState p.2) p.1 x) =
      fun p => riemannKernelReal (x - p.2) * (riemannKernelReal (x + p.1) +
        riemannKernelReal (x - p.1)) - riemannKernelReal x *
          (riemannKernelReal (x - p.2 + p.1) + riemannKernelReal (x - p.2 - p.1)) :=
    funext fun p => twoSidedShiftGenerator_translateGroundState p.2 p.1 x
  rw [e]
  exact ((hΦ.comp (continuous_const.sub continuous_snd)).mul
    ((hΦ.comp (continuous_const.add continuous_fst)).add
      (hΦ.comp (continuous_const.sub continuous_fst)))).sub
    (continuous_const.mul ((hΦ.comp ((continuous_const.sub continuous_snd).add continuous_fst)).add
      (hΦ.comp ((continuous_const.sub continuous_snd).sub continuous_fst))))

theorem continuous_twoSidedShiftGenerator_translate (t x : ℝ) :
    Continuous fun b => twoSidedShiftGenerator (translateGroundState b) t x := by
  have hΦ := continuous_riemannKernelReal
  have e : (fun b => twoSidedShiftGenerator (translateGroundState b) t x) =
      fun b => riemannKernelReal (x - b) * (riemannKernelReal (x + t) + riemannKernelReal (x - t)) -
        riemannKernelReal x * (riemannKernelReal (x - b + t) + riemannKernelReal (x - b - t)) :=
    funext fun b => twoSidedShiftGenerator_translateGroundState b t x
  rw [e]
  exact ((hΦ.comp (continuous_const.sub continuous_id)).mul continuous_const).sub
    (continuous_const.mul ((hΦ.comp ((continuous_const.sub continuous_id).add continuous_const)).add
      (hΦ.comp ((continuous_const.sub continuous_id).sub continuous_const))))

section Superposition

variable {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ)
include hφ hφc

theorem integrable_archLevy_mul_translate_prod (x : ℝ) :
    Integrable (Function.uncurry fun t b =>
      archLevyDensity t * (φ b * twoSidedShiftGenerator (translateGroundState b) t x))
      ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
  have hφi : Integrable fun b => |φ b| := (hφ.continuous.integrable_of_hasCompactSupport hφc).abs
  have hmaj : Integrable (fun p : ℝ × ℝ =>
      (4 * riemannKernelReal 0 * gammaSourceBound p.1) * |φ p.2|)
      ((volume.restrict (Ioi (0 : ℝ))).prod volume) :=
    (gammaSourceBound_integrable.const_mul _).mul_prod hφi
  refine hmaj.mono' ?_ ?_
  · exact ((measurable_archLevyDensity.comp measurable_fst).mul
      ((hφ.continuous.comp continuous_snd).mul
        (continuous_twoSidedShiftGenerator_translate_uncurry x)).measurable).aestronglyMeasurable
  · rw [Measure.restrict_prod_eq_prod_univ]
    refine ae_restrict_of_forall_mem (measurableSet_Ioi.prod MeasurableSet.univ) fun p hp => ?_
    have ht : 0 < p.1 := hp.1
    have hb := abs_archLevy_mul_twoSidedShiftGenerator_translateGroundState_le p.2 x ht
    show ‖archLevyDensity p.1 * (φ p.2 * twoSidedShiftGenerator (translateGroundState p.2) p.1 x)‖ ≤ _
    rw [Real.norm_eq_abs, show archLevyDensity p.1 * (φ p.2 *
      twoSidedShiftGenerator (translateGroundState p.2) p.1 x) = φ p.2 * (archLevyDensity p.1 *
        twoSidedShiftGenerator (translateGroundState p.2) p.1 x) by ring, abs_mul]
    nlinarith [mul_le_mul_of_nonneg_left hb (abs_nonneg (φ p.2))]

/-- The archimedean part of `𝓛_D ω_φ` is the superposition of those of the translates. -/
theorem integral_archLevy_twoSidedShiftGenerator_convGauge (x : ℝ) :
    (∫ t in Ioi (0 : ℝ), archLevyDensity t * twoSidedShiftGenerator (convGauge φ) t x) =
      ∫ b, φ b * ∫ t in Ioi (0 : ℝ), archLevyDensity t *
        twoSidedShiftGenerator (translateGroundState b) t x := by
  have hint := integrable_archLevy_mul_translate_prod hφ hφc x
  have h1 : (∫ t in Ioi (0 : ℝ), archLevyDensity t * twoSidedShiftGenerator (convGauge φ) t x) =
      ∫ t in Ioi (0 : ℝ), ∫ b, archLevyDensity t *
        (φ b * twoSidedShiftGenerator (translateGroundState b) t x) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [twoSidedShiftGenerator_convGauge hφ.continuous hφc, ← integral_const_mul]
  rw [h1, integral_integral_swap hint]
  refine integral_congr_ae (Eventually.of_forall fun b => ?_)
  simp only
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  ring

theorem integrable_mul_archTwoSidedGenerator_translate (x : ℝ) :
    Integrable fun b => φ b * ∫ t in Ioi (0 : ℝ), archLevyDensity t *
      twoSidedShiftGenerator (translateGroundState b) t x := by
  have h := (integrable_archLevy_mul_translate_prod hφ hφc x).integral_prod_right
  refine h.congr (Eventually.of_forall fun b => ?_)
  simp only [Function.uncurry_apply_pair]
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  ring

/-- The prime part of `𝓛_D ω_φ` is the superposition of those of the translates. -/
theorem tsum_atom_twoSidedShiftGenerator_convGauge (x : ℝ) :
    (∑' n : ℕ, vonMangoldtAtom n * twoSidedShiftGenerator (convGauge φ) (Real.log n) x) =
      ∫ b, φ b * ∑' n : ℕ, vonMangoldtAtom n *
        twoSidedShiftGenerator (translateGroundState b) (Real.log n) x := by
  obtain ⟨Rφ, -, hsupp⟩ := exists_support_radius hφc
  have hφi : Integrable fun b => |φ b| := (hφ.continuous.integrable_of_hasCompactSupport hφc).abs
  set K := 4 * riemannKernelReal 0 * (riemannKernelReal 0 / riemannKernelReal (|x| + Rφ))
  set F : ℕ → ℝ → ℝ := fun n b =>
    vonMangoldtAtom n * (φ b * twoSidedShiftGenerator (translateGroundState b) (Real.log n) x)
    with hF_def
  have hFint : ∀ n, Integrable (F n) := fun n => by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact continuous_const.mul (hφ.continuous.mul
        (continuous_twoSidedShiftGenerator_translate _ x))
    · exact (hφc.mul_right).mul_left
  have hbound : ∀ n b, |F n b| ≤ K * (vonMangoldtAtom n * riemannKernelReal (|x| + Rφ - Real.log n))
      * |φ b| := fun n b => by
    by_cases hb : |b| ≤ Rφ
    · have h := abs_atom_twoSidedShiftGenerator_translateGroundState_le (x := x) hb n
      simp only [hF_def]
      rw [show vonMangoldtAtom n * (φ b * twoSidedShiftGenerator (translateGroundState b)
        (Real.log n) x) = φ b * (vonMangoldtAtom n * twoSidedShiftGenerator (translateGroundState b)
          (Real.log n) x) by ring, abs_mul]
      nlinarith [mul_le_mul_of_nonneg_left h (abs_nonneg (φ b))]
    · simp only [hF_def]
      rw [hsupp b (not_le.mp hb)]
      simp
  have hsum : Summable fun n => ∫ b, ‖F n b‖ := by
    have hmaj : Summable fun n : ℕ =>
        K * (vonMangoldtAtom n * riemannKernelReal (|x| + Rφ - Real.log n)) * ∫ b, |φ b| :=
      ((summable_atom_mul_kernel_sub (|x| + Rφ)).mul_left K).mul_right _
    refine hmaj.of_nonneg_of_le (fun n => integral_nonneg fun b => norm_nonneg _) fun n => ?_
    rw [← integral_const_mul]
    exact integral_mono (hFint n).norm (hφi.const_mul _) fun b => by
      simpa [Real.norm_eq_abs] using hbound n b
  have h1 : (∑' n : ℕ, vonMangoldtAtom n * twoSidedShiftGenerator (convGauge φ) (Real.log n) x) =
      ∑' n : ℕ, ∫ b, F n b := by
    refine tsum_congr fun n => ?_
    rw [twoSidedShiftGenerator_convGauge hφ.continuous hφc, ← integral_const_mul]
  rw [h1, integral_tsum_of_summable_integral_norm hFint hsum]
  refine integral_congr_ae (Eventually.of_forall fun b => ?_)
  simp only [hF_def]
  rw [← tsum_mul_left]
  exact tsum_congr fun n => by ring

theorem integrable_mul_primeTwoSidedGenerator_translate (x : ℝ) :
    Integrable fun b => φ b * ∑' n : ℕ, vonMangoldtAtom n *
      twoSidedShiftGenerator (translateGroundState b) (Real.log n) x := by
  obtain ⟨Rφ, -, hsupp⟩ := exists_support_radius hφc
  have hφi : Integrable fun b => |φ b| := (hφ.continuous.integrable_of_hasCompactSupport hφc).abs
  set K := 4 * riemannKernelReal 0 * (riemannKernelReal 0 / riemannKernelReal (|x| + Rφ))
  set S := ∑' n : ℕ, vonMangoldtAtom n * riemannKernelReal (|x| + Rφ - Real.log n)
  have hterm : ∀ n b, |φ b * (vonMangoldtAtom n *
      twoSidedShiftGenerator (translateGroundState b) (Real.log n) x)| ≤
      K * (vonMangoldtAtom n * riemannKernelReal (|x| + Rφ - Real.log n)) * |φ b| := fun n b => by
    by_cases hb : |b| ≤ Rφ
    · have h := abs_atom_twoSidedShiftGenerator_translateGroundState_le (x := x) hb n
      rw [abs_mul]
      nlinarith [mul_le_mul_of_nonneg_left h (abs_nonneg (φ b))]
    · rw [hsupp b (not_le.mp hb)]
      simp
  have hmeas : AEStronglyMeasurable (fun b => φ b * ∑' n : ℕ, vonMangoldtAtom n *
      twoSidedShiftGenerator (translateGroundState b) (Real.log n) x) volume := by
    refine aestronglyMeasurable_of_tendsto_ae (f := fun N b => φ b *
      ∑ n ∈ Finset.range N, vonMangoldtAtom n *
        twoSidedShiftGenerator (translateGroundState b) (Real.log n) x)
      atTop (fun N => ?_) (Eventually.of_forall fun b => ?_)
    · exact (hφ.continuous.mul (continuous_finsetSum _ fun n _ => continuous_const.mul
        (continuous_twoSidedShiftGenerator_translate _ x))).aestronglyMeasurable
    · exact ((summable_atom_twoSidedShiftGenerator_translateGroundState b x).hasSum.tendsto_sum_nat).const_mul _
  refine (hφi.const_mul (K * S)).mono' hmeas (Eventually.of_forall fun b => ?_)
  rw [Real.norm_eq_abs, ← tsum_mul_left]
  have hB : Summable fun n : ℕ =>
      K * (vonMangoldtAtom n * riemannKernelReal (|x| + Rφ - Real.log n)) * |φ b| :=
    ((summable_atom_mul_kernel_sub (|x| + Rφ)).mul_left K).mul_right _
  have hnorm : Summable fun n : ℕ => ‖φ b * (vonMangoldtAtom n *
      twoSidedShiftGenerator (translateGroundState b) (Real.log n) x)‖ :=
    hB.of_nonneg_of_le (fun n => norm_nonneg _) fun n => by rw [Real.norm_eq_abs]; exact hterm n b
  calc |∑' n : ℕ, φ b * (vonMangoldtAtom n *
        twoSidedShiftGenerator (translateGroundState b) (Real.log n) x)|
      ≤ ∑' n : ℕ, ‖φ b * (vonMangoldtAtom n *
          twoSidedShiftGenerator (translateGroundState b) (Real.log n) x)‖ := by
        rw [← Real.norm_eq_abs]
        exact norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n : ℕ, K * (vonMangoldtAtom n * riemannKernelReal (|x| + Rφ - Real.log n)) * |φ b| :=
        Summable.tsum_le_tsum (fun n => by rw [Real.norm_eq_abs]; exact hterm n b) hnorm hB
    _ = K * S * |φ b| := by rw [tsum_mul_right, tsum_mul_left]

/-- **Superposition of the generator.** `𝓛_D ω_φ (x) = ∫ φ(b) 𝓛_D τ_b (x) db`. -/
theorem twoSidedGenerator_convGauge (x : ℝ) :
    twoSidedGenerator (convGauge φ) x =
      ∫ b, φ b * twoSidedGenerator (translateGroundState b) x := by
  unfold twoSidedGenerator
  rw [integral_archLevy_twoSidedShiftGenerator_convGauge hφ hφc,
    tsum_atom_twoSidedShiftGenerator_convGauge hφ hφc,
    ← integral_add (integrable_mul_archTwoSidedGenerator_translate hφ hφc x)
      (integrable_mul_primeTwoSidedGenerator_translate hφ hφc x)]
  refine integral_congr_ae (Eventually.of_forall fun b => ?_)
  simp only
  ring

/-- The source of the convolution gauge, `−∫ φ(b) cosh((x − b)/2) db`. -/
def convSource (φ : ℝ → ℝ) (x : ℝ) : ℝ := -∫ b, φ b * Real.cosh ((x - b) / 2)

omit hφ in
theorem integrable_mul_cosh_sub_half (hφc' : Continuous φ) (x : ℝ) :
    Integrable fun b => φ b * Real.cosh ((x - b) / 2) :=
  (hφc'.mul (Real.continuous_cosh.comp ((continuous_const.sub continuous_id).div_const 2))).integrable_of_hasCompactSupport
    hφc.mul_right

/-- **Source equation of the convolution gauge.**
`𝓛_D ω_φ − Φ cosh(x/2) ω_φ = Φ(x) · (−∫ φ(b) cosh((x − b)/2) db)`. -/
theorem twoSidedGenerator_convGauge_sub_potential (x : ℝ) :
    twoSidedGenerator (convGauge φ) x - riemannKernelReal x * Real.cosh (x / 2) * convGauge φ x =
      riemannKernelReal x * convSource φ x := by
  rw [twoSidedGenerator_convGauge hφ hφc]
  have hτ : ∀ b, twoSidedGenerator (translateGroundState b) x =
      riemannKernelReal x * Real.cosh (x / 2) * translateGroundState b x +
        riemannKernelReal x * -Real.cosh ((x - b) / 2) := fun b => by
    have := twoSidedGenerator_translateGroundState_sub_potential b x
    linarith
  simp_rw [hτ]
  have hi1 : Integrable fun b => φ b * (riemannKernelReal x * Real.cosh (x / 2) *
      translateGroundState b x) := by
    have e : (fun b => φ b * (riemannKernelReal x * Real.cosh (x / 2) * translateGroundState b x)) =
        fun b => (Real.cosh (x / 2)) * (φ b * riemannKernelReal (x - b)) := funext fun b => by
      rw [← riemannKernelReal_mul_translateGroundState]
      ring
    rw [e]
    exact (integrable_mul_riemannKernelReal_sub hφ.continuous hφc x).const_mul _
  have hi2 : Integrable fun b => φ b * (riemannKernelReal x * -Real.cosh ((x - b) / 2)) := by
    have e : (fun b => φ b * (riemannKernelReal x * -Real.cosh ((x - b) / 2))) =
        fun b => (-riemannKernelReal x) * (φ b * Real.cosh ((x - b) / 2)) := funext fun b => by ring
    rw [e]
    exact (integrable_mul_cosh_sub_half hφc hφ.continuous x).const_mul _
  have e2 : (fun b => φ b * (riemannKernelReal x * Real.cosh (x / 2) * translateGroundState b x +
      riemannKernelReal x * -Real.cosh ((x - b) / 2))) = fun b =>
        φ b * (riemannKernelReal x * Real.cosh (x / 2) * translateGroundState b x) +
          φ b * (riemannKernelReal x * -Real.cosh ((x - b) / 2)) := funext fun b => by ring
  rw [e2, integral_add hi1 hi2]
  have h1 : (∫ b, φ b * (riemannKernelReal x * Real.cosh (x / 2) * translateGroundState b x)) =
      riemannKernelReal x * Real.cosh (x / 2) * convGauge φ x := by
    have e : (fun b => φ b * (riemannKernelReal x * Real.cosh (x / 2) * translateGroundState b x)) =
        fun b => (Real.cosh (x / 2)) * (φ b * riemannKernelReal (x - b)) := funext fun b => by
      rw [← riemannKernelReal_mul_translateGroundState]
      ring
    rw [e, integral_const_mul, show (∫ b, φ b * riemannKernelReal (x - b)) = thetaConv φ x from rfl,
      ← riemannKernelReal_mul_convGauge]
    ring
  have h2 : (∫ b, φ b * (riemannKernelReal x * -Real.cosh ((x - b) / 2))) =
      riemannKernelReal x * convSource φ x := by
    unfold convSource
    rw [← integral_neg, ← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun b => by ring)
  rw [h1, h2]
  ring

/-- The archimedean shifts of the convolution gauge converge. -/
theorem integrableOn_archLevy_twoSidedShiftGenerator_convGauge (x : ℝ) :
    IntegrableOn (fun t => archLevyDensity t * twoSidedShiftGenerator (convGauge φ) t x) (Ioi 0) := by
  have h := (integrable_archLevy_mul_translate_prod hφ hφc x).integral_prod_left
  refine h.congr (Eventually.of_forall fun t => ?_)
  simp only [Function.uncurry_apply_pair]
  rw [twoSidedShiftGenerator_convGauge hφ.continuous hφc, ← integral_const_mul]

/-- The prime shifts of the convolution gauge are summable. -/
theorem summable_atom_twoSidedShiftGenerator_convGauge (x : ℝ) :
    Summable fun n : ℕ => vonMangoldtAtom n * twoSidedShiftGenerator (convGauge φ) (Real.log n) x := by
  obtain ⟨Rφ, -, hsupp⟩ := exists_support_radius hφc
  have hφi : Integrable fun b => |φ b| := (hφ.continuous.integrable_of_hasCompactSupport hφc).abs
  set K := 4 * riemannKernelReal 0 * (riemannKernelReal 0 / riemannKernelReal (|x| + Rφ))
  refine Summable.of_norm_bounded (((summable_atom_mul_kernel_sub (|x| + Rφ)).mul_left K).mul_right
    (∫ b, |φ b|)) fun n => ?_
  rw [twoSidedShiftGenerator_convGauge hφ.continuous hφc, ← integral_const_mul, Real.norm_eq_abs]
  refine (abs_integral_le_integral_abs).trans ?_
  rw [← integral_const_mul]
  refine integral_mono_of_nonneg (Eventually.of_forall fun b => abs_nonneg _) (hφi.const_mul _)
    (Eventually.of_forall fun b => ?_)
  by_cases hb : |b| ≤ Rφ
  · have h := abs_atom_twoSidedShiftGenerator_translateGroundState_le (x := x) hb n
    show |vonMangoldtAtom n * (φ b * twoSidedShiftGenerator (translateGroundState b) (Real.log n) x)|
      ≤ K * (vonMangoldtAtom n * riemannKernelReal (|x| + Rφ - Real.log n)) * |φ b|
    rw [show vonMangoldtAtom n * (φ b * twoSidedShiftGenerator (translateGroundState b)
      (Real.log n) x) = φ b * (vonMangoldtAtom n * twoSidedShiftGenerator (translateGroundState b)
        (Real.log n) x) by ring, abs_mul]
    nlinarith [mul_le_mul_of_nonneg_left h (abs_nonneg (φ b))]
  · show |vonMangoldtAtom n * (φ b * twoSidedShiftGenerator (translateGroundState b) (Real.log n) x)|
      ≤ K * (vonMangoldtAtom n * riemannKernelReal (|x| + Rφ - Real.log n)) * |φ b|
    rw [hsupp b (not_le.mp hb)]
    simp

/-- The theta convolution decays like `e^{−24|y|}`. -/
theorem exists_abs_thetaConv_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y, |riemannKernelReal y * convGauge φ y| ≤ C * Real.exp (-(24 * |y|)) := by
  obtain ⟨C₀, hC₀, hC⟩ := exists_riemannKernelReal_le_exp_twentyFour
  obtain ⟨Rφ, -, hsupp⟩ := exists_support_radius hφc
  have hφi : Integrable fun b => |φ b| := (hφ.continuous.integrable_of_hasCompactSupport hφc).abs
  refine ⟨C₀ * Real.exp (24 * Rφ) * ∫ b, |φ b|,
    mul_nonneg (by positivity) (integral_nonneg fun b => abs_nonneg _), fun y => ?_⟩
  rw [riemannKernelReal_mul_convGauge]
  unfold thetaConv
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le (hφi.const_mul (C₀ * Real.exp (24 * Rφ) *
    Real.exp (-(24 * |y|)))) (Eventually.of_forall fun b => ?_)).trans_eq ?_
  · rw [Real.norm_eq_abs, abs_mul, abs_of_pos (riemannKernelReal_pos _)]
    by_cases hb : |b| ≤ Rφ
    · have h1 := hC (y - b)
      have h2 := exp_neg_mul_abs_sub_le 24 y b (by norm_num)
      have h3 : Real.exp (24 * |b|) ≤ Real.exp (24 * Rφ) := Real.exp_le_exp.mpr (by linarith)
      have hb0 := abs_nonneg (φ b)
      have : riemannKernelReal (y - b) ≤ C₀ * Real.exp (24 * Rφ) * Real.exp (-(24 * |y|)) := by
        refine h1.trans ?_
        calc C₀ * Real.exp (-(24 * |y - b|)) ≤ C₀ * (Real.exp (24 * |b|) * Real.exp (-(24 * |y|))) :=
              mul_le_mul_of_nonneg_left h2 hC₀
          _ ≤ C₀ * (Real.exp (24 * Rφ) * Real.exp (-(24 * |y|))) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le) hC₀
          _ = _ := by ring
      nlinarith [mul_le_mul_of_nonneg_left this hb0]
    · rw [hsupp b (not_le.mp hb)]
      simp
  · rw [integral_const_mul]
    ring

end Superposition

/-! ### The pole coefficients -/

/-- `A_φ = ∫ φ(b) cosh(b/2) db`. -/
def convCoshCoefficient (φ : ℝ → ℝ) : ℝ := ∫ b, φ b * Real.cosh (b / 2)

/-- `B_φ = ∫ φ(b) sinh(b/2) db`. -/
def convSinhCoefficient (φ : ℝ → ℝ) : ℝ := ∫ b, φ b * Real.sinh (b / 2)

section Coefficients

variable {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ)
include hφ hφc

theorem convSource_eq (x : ℝ) :
    convSource φ x = -(convCoshCoefficient φ * Real.cosh (x / 2) -
      convSinhCoefficient φ * Real.sinh (x / 2)) := by
  have hc : Integrable fun b => φ b * Real.cosh (b / 2) :=
    (hφ.continuous.mul (Real.continuous_cosh.comp (continuous_id.div_const 2))).integrable_of_hasCompactSupport
      hφc.mul_right
  have hs : Integrable fun b => φ b * Real.sinh (b / 2) :=
    (hφ.continuous.mul (Real.continuous_sinh.comp (continuous_id.div_const 2))).integrable_of_hasCompactSupport
      hφc.mul_right
  unfold convSource convCoshCoefficient convSinhCoefficient
  rw [← integral_mul_const, ← integral_mul_const, ← integral_sub (hc.mul_const _) (hs.mul_const _)]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun b => ?_)
  simp only
  rw [show (x - b) / 2 = x / 2 - b / 2 by ring, Real.cosh_sub]
  ring

theorem continuous_convSource : Continuous (convSource φ) := by
  have e : convSource φ = fun x => -(convCoshCoefficient φ * Real.cosh (x / 2) -
      convSinhCoefficient φ * Real.sinh (x / 2)) := funext (convSource_eq hφ hφc)
  rw [e]
  exact ((continuous_const.mul (Real.continuous_cosh.comp (continuous_id.div_const 2))).sub
    (continuous_const.mul (Real.continuous_sinh.comp (continuous_id.div_const 2)))).neg

theorem abs_convSource_le (x : ℝ) :
    |convSource φ x| ≤
      (|convCoshCoefficient φ| + |convSinhCoefficient φ|) * Real.exp (8 * |x|) := by
  have hc : |Real.cosh (x / 2)| ≤ Real.exp (8 * |x|) := by
    rw [abs_of_pos (Real.cosh_pos _)]
    exact (cosh_le_exp_abs _).trans (exp_abs_half_le_exp_eight x)
  have hs : |Real.sinh (x / 2)| ≤ Real.exp (8 * |x|) :=
    (abs_sinh_le_exp_abs _).trans (exp_abs_half_le_exp_eight x)
  rw [convSource_eq hφ hφc, abs_neg]
  refine (abs_sub _ _).trans ?_
  rw [abs_mul, abs_mul]
  nlinarith [mul_le_mul_of_nonneg_left hc (abs_nonneg (convCoshCoefficient φ)),
    mul_le_mul_of_nonneg_left hs (abs_nonneg (convSinhCoefficient φ))]

theorem integrable_thetaConv_mul_convSource :
    Integrable fun x => (riemannKernelReal x * convGauge φ x) * convSource φ x := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_thetaConv_le hφ hφc
  set H := |convCoshCoefficient φ| + |convSinhCoefficient φ|
  have hH0 : 0 ≤ H := add_nonneg (abs_nonneg _) (abs_nonneg _)
  refine (integrable_exp_neg_eight_mul_abs.const_mul (C * H)).mono' ?_
    (Eventually.of_forall fun x => ?_)
  · exact ((continuous_riemannKernelReal.mul (contDiff_convGauge hφ hφc).continuous).mul
      (continuous_convSource hφ hφc)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_mul]
    have he : Real.exp (-(24 * |x|)) * Real.exp (8 * |x|) ≤ Real.exp (-(8 * |x|)) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (by linarith [abs_nonneg x])
    calc |riemannKernelReal x * convGauge φ x| * |convSource φ x|
        ≤ (C * Real.exp (-(24 * |x|))) * (H * Real.exp (8 * |x|)) :=
          mul_le_mul (hC x) (abs_convSource_le hφ hφc x) (abs_nonneg _) (by positivity)
      _ = C * H * (Real.exp (-(24 * |x|)) * Real.exp (8 * |x|)) := by ring
      _ ≤ C * H * Real.exp (-(8 * |x|)) := mul_le_mul_of_nonneg_left he (by positivity)

/-- `∫ (Φ ∗ φ) g_φ = (B_φ² − A_φ²)/2`: the pole pairing of a theta convolution is the Lorentz form
of its pole coefficients. Fubini against the translate moments `∫ Φ(x − b) cosh(x/2) = cosh(b/2)/2`,
`∫ Φ(x − b) sinh(x/2) = sinh(b/2)/2`. -/
theorem integral_thetaConv_mul_convSource :
    (∫ x, (riemannKernelReal x * convGauge φ x) * convSource φ x) =
      (convSinhCoefficient φ ^ 2 - convCoshCoefficient φ ^ 2) / 2 := by
  set A := convCoshCoefficient φ with hA_def
  set B := convSinhCoefficient φ with hB_def
  obtain ⟨C₀, hC₀, hC⟩ := exists_riemannKernelReal_le_exp_twentyFour
  obtain ⟨R, -, hsupp⟩ := exists_support_radius hφc
  have hφi : Integrable fun b => |φ b| := (hφ.continuous.integrable_of_hasCompactSupport hφc).abs
  set H := |A| + |B|
  have hH0 : 0 ≤ H := add_nonneg (abs_nonneg _) (abs_nonneg _)
  set h : ℝ → ℝ := fun x => B * Real.sinh (x / 2) - A * Real.cosh (x / 2) with hh_def
  have hhc : Continuous h :=
    (continuous_const.mul (Real.continuous_sinh.comp (continuous_id.div_const 2))).sub
      (continuous_const.mul (Real.continuous_cosh.comp (continuous_id.div_const 2)))
  have hsrc : ∀ x, convSource φ x = h x := fun x => by
    rw [convSource_eq hφ hφc]
    simp only [hh_def]
    ring
  have hhb : ∀ x, |h x| ≤ H * Real.exp (8 * |x|) := fun x => by
    rw [← hsrc]
    exact abs_convSource_le hφ hφc x
  have hprod : Integrable (Function.uncurry fun x b => φ b * (riemannKernelReal (x - b) * h x))
      (volume.prod volume) := by
    have hmaj : Integrable (fun p : ℝ × ℝ =>
        (C₀ * Real.exp (24 * R) * H * Real.exp (-(8 * |p.1|))) * |φ p.2|) (volume.prod volume) :=
      (integrable_exp_neg_eight_mul_abs.const_mul (C₀ * Real.exp (24 * R) * H)).mul_prod hφi
    refine hmaj.mono' ?_ (Eventually.of_forall fun p => ?_)
    · exact ((hφ.continuous.comp continuous_snd).mul
        ((continuous_riemannKernelReal.comp (continuous_fst.sub continuous_snd)).mul
          (hhc.comp continuous_fst))).aestronglyMeasurable
    · show ‖φ p.2 * (riemannKernelReal (p.1 - p.2) * h p.1)‖ ≤ _
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (riemannKernelReal_pos _)]
      by_cases hb : |p.2| ≤ R
      · have h2 := exp_neg_mul_abs_sub_le 24 p.1 p.2 (by norm_num)
        have h3 : Real.exp (24 * |p.2|) ≤ Real.exp (24 * R) := Real.exp_le_exp.mpr (by linarith)
        have hk : riemannKernelReal (p.1 - p.2) ≤
            C₀ * Real.exp (24 * R) * Real.exp (-(24 * |p.1|)) := by
          refine (hC (p.1 - p.2)).trans ?_
          calc C₀ * Real.exp (-(24 * |p.1 - p.2|))
              ≤ C₀ * (Real.exp (24 * |p.2|) * Real.exp (-(24 * |p.1|))) :=
                mul_le_mul_of_nonneg_left h2 hC₀
            _ ≤ C₀ * (Real.exp (24 * R) * Real.exp (-(24 * |p.1|))) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le) hC₀
            _ = _ := by ring
        have he : Real.exp (-(24 * |p.1|)) * Real.exp (8 * |p.1|) ≤ Real.exp (-(8 * |p.1|)) := by
          rw [← Real.exp_add]
          exact Real.exp_le_exp.mpr (by linarith [abs_nonneg p.1])
        have hkh : riemannKernelReal (p.1 - p.2) * |h p.1| ≤
            C₀ * Real.exp (24 * R) * H * Real.exp (-(8 * |p.1|)) :=
          calc riemannKernelReal (p.1 - p.2) * |h p.1|
              ≤ (C₀ * Real.exp (24 * R) * Real.exp (-(24 * |p.1|))) * (H * Real.exp (8 * |p.1|)) :=
                mul_le_mul hk (hhb p.1) (abs_nonneg _) (by positivity)
            _ = C₀ * Real.exp (24 * R) * H * (Real.exp (-(24 * |p.1|)) * Real.exp (8 * |p.1|)) := by
                ring
            _ ≤ _ := mul_le_mul_of_nonneg_left he (by positivity)
        nlinarith [mul_le_mul_of_nonneg_left hkh (abs_nonneg (φ p.2))]
      · rw [hsupp p.2 (not_le.mp hb)]
        simp
  have hconv : (fun x => (riemannKernelReal x * convGauge φ x) * convSource φ x) =
      fun x => ∫ b, φ b * (riemannKernelReal (x - b) * h x) := funext fun x => by
    rw [riemannKernelReal_mul_convGauge, hsrc]
    unfold thetaConv
    rw [← integral_mul_const]
    exact integral_congr_ae (Eventually.of_forall fun b => by ring)
  have hin : (∫ b, ∫ x, φ b * (riemannKernelReal (x - b) * h x)) =
      ∫ b, (B / 2) * (φ b * Real.sinh (b / 2)) - (A / 2) * (φ b * Real.cosh (b / 2)) := by
    refine integral_congr_ae (Eventually.of_forall fun b => ?_)
    simp only [hh_def]
    have e : (fun x => φ b * (riemannKernelReal (x - b) *
        (B * Real.sinh (x / 2) - A * Real.cosh (x / 2)))) = fun x =>
          (φ b * B) * (riemannKernelReal (x - b) * Real.sinh (x / 2)) -
            (φ b * A) * (riemannKernelReal (x - b) * Real.cosh (x / 2)) := funext fun x => by ring
    rw [e, integral_sub ((integrable_riemannKernelReal_sub_mul_sinh_half b).const_mul _)
      ((integrable_riemannKernelReal_sub_mul_cosh_half b).const_mul _), integral_const_mul,
      integral_const_mul, integral_riemannKernelReal_sub_mul_sinh_half,
      integral_riemannKernelReal_sub_mul_cosh_half]
    ring
  have hc : Integrable fun b => φ b * Real.cosh (b / 2) :=
    (hφ.continuous.mul (Real.continuous_cosh.comp (continuous_id.div_const 2))).integrable_of_hasCompactSupport
      hφc.mul_right
  have hs : Integrable fun b => φ b * Real.sinh (b / 2) :=
    (hφ.continuous.mul (Real.continuous_sinh.comp (continuous_id.div_const 2))).integrable_of_hasCompactSupport
      hφc.mul_right
  rw [hconv, integral_integral_swap hprod, hin, integral_sub (hs.const_mul _) (hc.const_mul _),
    integral_const_mul, integral_const_mul]
  change B / 2 * B - A / 2 * A = _
  ring

/-- **The Lorentz law for theta convolutions.** There is `K` with
`|markovEnergy(Φ(ω_φ u_L)) − (B_φ² − A_φ²)/2| ≤ K e^{−8L}` for all `L`. -/
theorem exists_abs_markovEnergy_convPlateau_sub_le :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ L : ℝ,
      |markovEnergy (fun x => (phiDoobTest (fun y => convGauge φ y * smoothPlateau L y) x : ℂ)) -
        (convSinhCoefficient φ ^ 2 - convCoshCoefficient φ ^ 2) / 2| ≤ K * Real.exp (-(8 * L)) := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_thetaConv_le hφ hφc
  obtain ⟨Λ, hΛ0, hΛ⟩ := exists_smoothPlateau_lipschitz
  set H := |convCoshCoefficient φ| + |convSinhCoefficient φ|
  have hH0 : 0 ≤ H := add_nonneg (abs_nonneg _) (abs_nonneg _)
  set I₈ := ∫ x : ℝ, Real.exp (-(8 * |x|))
  have hI₈0 : 0 ≤ I₈ := integral_nonneg fun x => (Real.exp_pos _).le
  set K₁ := C ^ 2 * (2 * Λ * archFirstMoment + 2 * primeEighthMoment)
  have hK₁0 : 0 ≤ K₁ := by
    have := archFirstMoment_nonneg
    have := primeEighthMoment_nonneg
    positivity
  have hgen := abs_markovEnergy_plateau_sub_integral_le (contDiff_convGauge hφ hφc) hC0 hC hΛ0 hΛ
    (integrableOn_archLevy_twoSidedShiftGenerator_convGauge hφ hφc)
    (summable_atom_twoSidedShiftGenerator_convGauge hφ hφc)
    (twoSidedGenerator_convGauge_sub_potential hφ hφc) (continuous_convSource hφ hφc)
  refine ⟨K₁ * I₈ + C * H * I₈, by positivity, fun L => ?_⟩
  have hu := (contDiff_smoothPlateau L).continuous
  have hMc : Continuous fun x => riemannKernelReal x * convGauge φ x :=
    continuous_riemannKernelReal.mul (contDiff_convGauge hφ hφc).continuous
  have hAi : Integrable fun x => smoothPlateau L x ^ 2 * (riemannKernelReal x * convGauge φ x) *
      convSource φ x := by
    refine Continuous.integrable_of_hasCompactSupport (((hu.pow 2).mul hMc).mul
      (continuous_convSource hφ hφc)) ?_
    exact ((hasCompactSupport_sq (hasCompactSupport_smoothPlateau L)).mul_right).mul_right
  have hpole : |(∫ x, smoothPlateau L x ^ 2 * (riemannKernelReal x * convGauge φ x) *
      convSource φ x) - (convSinhCoefficient φ ^ 2 - convCoshCoefficient φ ^ 2) / 2| ≤
      C * H * Real.exp (-(8 * L)) * I₈ := by
    rw [← integral_thetaConv_mul_convSource hφ hφc,
      ← integral_sub hAi (integrable_thetaConv_mul_convSource hφ hφc), ← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le (integrable_exp_neg_eight_mul_abs.const_mul
      (C * H * Real.exp (-(8 * L)))) (Eventually.of_forall fun x => ?_)).trans_eq ?_
    · rw [Real.norm_eq_abs, show smoothPlateau L x ^ 2 * (riemannKernelReal x * convGauge φ x) *
          convSource φ x - riemannKernelReal x * convGauge φ x * convSource φ x =
          (smoothPlateau L x ^ 2 - 1) * ((riemannKernelReal x * convGauge φ x) * convSource φ x) by
            ring]
      exact abs_smoothPlateau_sq_sub_one_mul_le_of_growth hC0 hH0 hC (abs_convSource_le hφ hφc) L x
    · rw [integral_const_mul]
  calc _ ≤ K₁ * I₈ * Real.exp (-(8 * L)) + C * H * Real.exp (-(8 * L)) * I₈ :=
        (abs_sub_le _ _ _).trans (add_le_add (hgen L) hpole)
    _ = (K₁ * I₈ + C * H * I₈) * Real.exp (-(8 * L)) := by ring

theorem tendsto_markovEnergy_convPlateau :
    Tendsto (fun L => markovEnergy (fun x =>
        (phiDoobTest (fun y => convGauge φ y * smoothPlateau L y) x : ℂ))) atTop
      (𝓝 ((convSinhCoefficient φ ^ 2 - convCoshCoefficient φ ^ 2) / 2)) := by
  obtain ⟨K, -, hK⟩ := exists_abs_markovEnergy_convPlateau_sub_le hφ hφc
  exact tendsto_of_abs_sub_le (Eventually.of_forall hK)

/-! ### Harmonic theta convolutions -/

/-- `A_φ = B_φ = 0` makes `ω_φ` harmonic: `𝓛_D ω_φ = Φ cosh(x/2) ω_φ`. -/
theorem twoSidedGenerator_convGauge_of_harmonic (hA : convCoshCoefficient φ = 0)
    (hB : convSinhCoefficient φ = 0) (x : ℝ) :
    twoSidedGenerator (convGauge φ) x = riemannKernelReal x * Real.cosh (x / 2) * convGauge φ x := by
  have h := twoSidedGenerator_convGauge_sub_potential hφ hφc x
  rw [convSource_eq hφ hφc, hA, hB] at h
  linarith

/-- **Harmonic theta convolutions lie in the radical.** For `A_φ = B_φ = 0` and every
`v ∈ C²_c(ℝ)`, `|markovEnergy(Φ(ω_φ u_L + v)) − markovEnergy(Φ v)| ≤ K e^{−8L}` for `L ≥ R`. -/
theorem exists_abs_markovEnergy_add_convPlateau_sub_le_of_harmonic
    (hA : convCoshCoefficient φ = 0) (hB : convSinhCoefficient φ = 0)
    {v : ℝ → ℝ} (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v) :
    ∃ K R : ℝ, 0 ≤ K ∧ ∀ L, R ≤ L →
      |markovEnergy (fun x => (phiDoobTest (fun y => convGauge φ y * smoothPlateau L y + v y) x : ℂ)) -
        markovEnergy (fun x => (phiDoobTest v x : ℂ))| ≤ K * Real.exp (-(8 * L)) := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_thetaConv_le hφ hφc
  exact abs_markovEnergy_add_harmonicPlateau_sub_le (contDiff_convGauge hφ hφc) hC0 hC
    (integrableOn_archLevy_twoSidedShiftGenerator_convGauge hφ hφc)
    (summable_atom_twoSidedShiftGenerator_convGauge hφ hφc)
    (twoSidedGenerator_convGauge_of_harmonic hφ hφc hA hB) hv hvc

/-! ### Ground-state representation in the convolution gauge -/

/-- `markovEnergy(Φ(ω_φ u)) = J_{Φ∗φ}(u) − ∫ u² (Φ ∗ φ)(A_φ cosh(x/2) − B_φ sinh(x/2))` for every
`u ∈ C²_c(ℝ)`: the conductances are `(Φ ∗ φ)(x)(Φ ∗ φ)(x + t)`. -/
theorem markovEnergy_phiDoob_convGauge_mul_eq {u : ℝ → ℝ} (hu : ContDiff ℝ 2 u)
    (huc : HasCompactSupport u) :
    markovEnergy (fun x => (phiDoobTest (fun y => convGauge φ y * u y) x : ℂ)) =
      signedJumpEnergy (thetaConv φ) u + ∫ x, u x ^ 2 * thetaConv φ x * convSource φ x := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_thetaConv_le hφ hφc
  have h := markovEnergy_phiDoob_mul_eq_signedJump_add_source (contDiff_convGauge hφ hφc) hC0 hC
    (integrableOn_archLevy_twoSidedShiftGenerator_convGauge hφ hφc)
    (summable_atom_twoSidedShiftGenerator_convGauge hφ hφc)
    (twoSidedGenerator_convGauge_sub_potential hφ hφc) (continuous_convSource hφ hφc) hu huc
  simp only [riemannKernelReal_mul_convGauge] at h
  exact h

/-- **Harmonic theta convolutions are potential-free.** For `A_φ = B_φ = 0`,
`markovEnergy(Φ(ω_φ u)) = J_{Φ∗φ}(u)` for every `u ∈ C²_c(ℝ)`. -/
theorem markovEnergy_phiDoob_convGauge_mul_eq_signedJump_of_harmonic
    (hA : convCoshCoefficient φ = 0) (hB : convSinhCoefficient φ = 0) {u : ℝ → ℝ}
    (hu : ContDiff ℝ 2 u) (huc : HasCompactSupport u) :
    markovEnergy (fun x => (phiDoobTest (fun y => convGauge φ y * u y) x : ℂ)) =
      signedJumpEnergy (thetaConv φ) u := by
  rw [markovEnergy_phiDoob_convGauge_mul_eq hφ hφc hu huc]
  have h0 : ∀ x, convSource φ x = 0 := fun x => by
    rw [convSource_eq hφ hφc, hA, hB]
    ring
  simp [h0]

end Coefficients

end GaloisForLFunctions.ArithmeticCriticalityTheory

end
