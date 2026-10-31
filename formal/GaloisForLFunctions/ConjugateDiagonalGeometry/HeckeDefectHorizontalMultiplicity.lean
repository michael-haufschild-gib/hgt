import GaloisForLFunctions.ConjugateDiagonalGeometry.CollisionChargeIncrements
import GaloisForLFunctions.ConjugateDiagonalGeometry.ZetaDepthDistribution
import GaloisForLFunctions.ArithmeticPolarization.TheLocalWeylLawOfTheCollidedForm
import GaloisForLFunctions.SquareRootThreshold.WindowedExcursionBalanceAndDoubleWindowRealVarianceLaw

/-!
# Prime-side and Hecke-defect bounds on horizontal fibre multiplicity and collision increments

Let `H(γ) = xiHorizontalMultiplicity γ` be the total divisor multiplicity of `ξ` along the
horizontal line `Im ρ = γ` (`0 < Re ρ < 1`), and `ΔO(T) = xiCollisionIncrement T` the unit-window
increment of the horizontal collision charge `O(T)`.

1. **Off-line fibre reduction of `ΔO(T)`** (`xiCollisionIncrement_le_max_fibre_mul_unitWindowOrder`,
   `xiCollisionIncrement_le_two_mul_max_offLineFibre_mul_offLineOrder`):
   Every critical zero on an ordinate with no off-line zero contributes `0` to `ΔO(T)`. If
   `H(Im ρ) ≤ B` for every off-line zero `ρ` in `[T, T + 1)`, then `ΔO(T) ≤ 2 B n_off(T)`, which is
   `O(B log T)` by the local zero-density bound `n_off(T) ≤ n(T) ≤ C log T`.

2. **Continuous Hecke-averaged bump and hyperbolic `cosh` fibre coercivity**
   (`one_le_re_tr_twist_of_im_eq`, `horizontalMultiplicity_le_collidedForm_heckeAvg`):
   Averaging a smooth, even, nonnegative, unit-integral bump `h` supported in `[-1/4, 1/4]` across
   translations `[-L, L]` produces `F_L(u) = (2L)⁻¹ ∫_{u-L}^{u+L} h(v) dv` supported in
   `[-(L + 1/4), L + 1/4]` with `∫ F_L = 1`, `∫ ‖F_L‖² ≤ (2L)⁻¹`, and uniformly bounded `C²`
   envelope for `L ≥ 1`. At every zero `ρ = 1/2 + δ_ρ + iγ` on `Im ρ = γ`, evenness and `F_L ≥ 0`
   give `tr (twist γ F_L) ρ = ∫ F_L(u) cosh(δ_ρ u) du ≥ 1`, whence `H(γ) ≤ D(twist γ F_L)`.

3. **Sinc-cancelled off-line defect bound** (`offLineDefect_heckeAvg_le_heckeDefect_add_lorentz`):
   Splitting the translation phase difference into its static mismatch `u_ρ − v_ρ` (cancelled at
   rate `O(L⁻¹ (1 + |Im ρ − γ|²)⁻¹/²)` by `(2L)⁻¹ ∫_{-L}^L e^{iℓω} dℓ` and vanishing on `Im ρ = γ`)
   and its depth-variation part `(e^{ℓδ_ρ} − 1)u_ρ − (e^{−ℓδ_ρ} − 1)v_ρ` bounds
   `Δ(twist γ F_L) ≤ 4 heckeDefect (baseTwistTest γ) L + C (1 + log(|γ| + 4)) / L²`.

4. **Master prime-polynomial + Hecke-defect inequality and scale corollaries**
   (`exists_horizontalMultiplicity_le_primePolynomial_add_heckeDefect`,
   `exists_xiCollisionIncrement_le_log_of_prime_and_heckeDefect_at_log_scale`,
   `exists_horizontalMultiplicity_le_log_div_log_log_add_heckeDefect`):
   For `1 ≤ L ≤ 4 log(1 + |γ|)`,
   `H(γ) ≤ C_* (1 + log(2 + |γ|) / L) − Re Π_{F_L}(⌊e^{2L + 1/2}⌋, −γ/2π) + 4 heckeDefect_γ(L)`.
   At `L = c log T` (`0 < c ≤ 4`), boundedness of `−Re Π_{F_L}` and `heckeDefect` across `[T, T + 1)`
   yields `H(γ) = O(1)` and `ΔO(T) ≪ log T`. At `L = (1/4) log log |γ|`, the prime polynomial is
   discharged unconditionally without prime cancellation, giving
   `H(γ) ≪ log |γ| / log log |γ| + heckeDefect_γ((1/4) log log |γ|)`.
-/

set_option autoImplicit false

open Complex Filter Topology Set MeasureTheory
open scoped BigOperators Real ComplexConjugate ContDiff
open _root_.RHTower _root_.Zeta23

noncomputable section

namespace GaloisForLFunctions.ConjugateDiagonalGeometry

open ArithmeticPolarization SquareRootThreshold

/-! ## §1. Combinatorial reduction of `ΔO(T)` to horizontal fibre multiplicity -/

/-- If `H(Im ρ) − 1 ≤ B` for every zero `ρ` in the unit window `[T, T + 1)`, then
`ΔO(T) ≤ B n(T)`. -/
theorem xiCollisionIncrement_le_max_fibre_mul_unitWindowOrder {T : ℝ} {B : ℕ}
    (hB : ∀ ρ ∈ xiUnitWindowZeros T, xiHorizontalMultiplicity ρ.im - 1 ≤ B) :
    xiCollisionIncrement T ≤ B * xiUnitWindowOrder T := by
  rw [xiCollisionIncrement_eq, xiUnitWindowOrder, Finset.mul_sum]
  refine Finset.sum_le_sum fun ρ hρ => ?_
  unfold xiCollisionTerm
  rcases Nat.eq_zero_or_pos (analyticOrderAt xi ρ).toNat with hm0 | hmpos
  · simp [hm0]
  · rw [mul_comm]
    refine Nat.mul_le_mul_right _ ?_
    have h1 := hB ρ hρ
    omega

/-- If `H(Im ρ) ≤ B` whenever `Im ρ` carries an off-line zero in `W(T)`, then
`ΔO(T) ≤ 2 B n_off(T)`. -/
theorem xiCollisionIncrement_le_two_mul_max_offLineFibre_mul_offLineOrder {T : ℝ} {B : ℕ}
    (hB : ∀ ρ ∈ xiUnitWindowZeros T, ρ.re ≠ 1 / 2 → xiHorizontalMultiplicity ρ.im ≤ B) :
    xiCollisionIncrement T ≤ 2 * B * xiUnitWindowOffLineOrder T := by
  classical
  rw [xiCollisionIncrement_eq]
  set W := xiUnitWindowZeros T
  set Woff := W.filter (fun ρ => ρ.re ≠ 1 / 2)
  set Wcrit := W.filter (fun ρ => ρ.re = 1 / 2)
  have hsplit : ∑ ρ ∈ W, xiCollisionTerm ρ =
      ∑ ρ ∈ Wcrit, xiCollisionTerm ρ + ∑ ρ ∈ Woff, xiCollisionTerm ρ :=
    (Finset.sum_filter_add_sum_filter_not W (fun ρ => ρ.re = 1 / 2) xiCollisionTerm).symm
  have hoff_le : ∑ ρ ∈ Woff, xiCollisionTerm ρ ≤ B * xiUnitWindowOffLineOrder T := by
    rw [xiUnitWindowOffLineOrder, Finset.mul_sum]
    refine Finset.sum_le_sum fun ρ hρ => ?_
    obtain ⟨hρW, hρne⟩ := Finset.mem_filter.mp hρ
    unfold xiCollisionTerm
    rw [mul_comm B]
    exact Nat.mul_le_mul_left _ ((Nat.sub_le _ _).trans (hB ρ hρW hρne))
  have hcrit_le : ∑ ρ ∈ Wcrit, xiCollisionTerm ρ ≤ B * xiUnitWindowOffLineOrder T := by
    have hterm : ∀ ρ ∈ Wcrit,
        xiCollisionTerm ρ =
          ∑ z ∈ Woff.filter (fun z => z.im = ρ.im),
            (analyticOrderAt xi ρ).toNat * (analyticOrderAt xi z).toNat := by
      intro ρ hρ
      obtain ⟨hρW, hρre⟩ := Finset.mem_filter.mp hρ
      obtain ⟨hρS, hTle⟩ := mem_xiUnitWindowZeros.mp hρW
      unfold xiCollisionTerm
      rw [horizontalMultiplicity_sub_order_eq_sum_same_im_erase hρS, Finset.mul_sum]
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext z
      simp only [Finset.mem_erase, Finset.mem_filter, Woff, W]
      constructor
      · rintro ⟨hzne, hzS, hzim⟩
        refine ⟨⟨mem_xiUnitWindowZeros_of_fibre hTle (Finset.mem_filter.mpr ⟨hzS, hzim⟩), ?_⟩, hzim⟩
        intro hzre
        exact hzne (Complex.ext (hzre.trans hρre.symm) hzim)
      · rintro ⟨⟨hzW, hzne⟩, hzim⟩
        refine ⟨?_, (mem_xiUnitWindowZeros.mp hzW).1, hzim⟩
        rintro rfl
        exact hzne hρre
    calc ∑ ρ ∈ Wcrit, xiCollisionTerm ρ
        = ∑ ρ ∈ Wcrit, ∑ z ∈ Woff.filter (fun z => z.im = ρ.im),
            (analyticOrderAt xi ρ).toNat * (analyticOrderAt xi z).toNat :=
          Finset.sum_congr rfl hterm
      _ = ∑ z ∈ Woff, ∑ ρ ∈ Wcrit.filter (fun ρ => z.im = ρ.im),
            (analyticOrderAt xi ρ).toNat * (analyticOrderAt xi z).toNat := by
          simp_rw [Finset.sum_filter]
          rw [Finset.sum_comm]
      _ ≤ ∑ z ∈ Woff, B * (analyticOrderAt xi z).toNat := by
          refine Finset.sum_le_sum fun z hz => ?_
          rw [← Finset.sum_mul]
          refine Nat.mul_le_mul_right _ ?_
          obtain ⟨hzW, hzne⟩ := Finset.mem_filter.mp hz
          obtain ⟨hzS, _⟩ := mem_xiUnitWindowZeros.mp hzW
          have hsub : Wcrit.filter (fun ρ => z.im = ρ.im) ⊆ stripHeightFinset z.im := by
            intro ρ hρ
            obtain ⟨hρc, hzim⟩ := Finset.mem_filter.mp hρ
            obtain ⟨hρW, _⟩ := Finset.mem_filter.mp hρc
            have hρS := (mem_xiUnitWindowZeros.mp hρW).1
            rw [stripHeightFinset_eq_stripZeros_filter_im hzS]
            exact Finset.mem_filter.mpr ⟨hρS, hzim.symm⟩
          exact (Finset.sum_le_sum_of_subset hsub).trans (hB z hzW hzne)
      _ = B * xiUnitWindowOffLineOrder T := by
          rw [← Finset.mul_sum]; rfl
  rw [hsplit]
  calc ∑ ρ ∈ Wcrit, xiCollisionTerm ρ + ∑ ρ ∈ Woff, xiCollisionTerm ρ
      ≤ B * xiUnitWindowOffLineOrder T + B * xiUnitWindowOffLineOrder T :=
        Nat.add_le_add hcrit_le hoff_le
    _ = 2 * B * xiUnitWindowOffLineOrder T := by ring

/-! ## §2. Normalized smooth even bump and continuous Hecke-averaged bump `F_L` -/

/-- Base `ContDiffBump` supported in `(-1/4, 1/4)` and equal to `1` on `[-1/8, 1/8]`. -/
def baseContDiffBump : ContDiffBump (0 : ℝ) := ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩

/-- Normalized real smooth bump `h₀` on `[-1/4, 1/4]`. -/
def baseBumpReal (u : ℝ) : ℝ := baseContDiffBump.normed volume u

/-- Complex-valued normalized smooth bump `h(u) = (h₀(u) : ℂ)`. -/
def baseBump (u : ℝ) : ℂ := (baseBumpReal u : ℂ)

theorem contDiff_baseBumpReal {n : ℕ∞} : ContDiff ℝ n baseBumpReal :=
  baseContDiffBump.contDiff_normed

theorem contDiff_baseBump {n : ℕ∞} : ContDiff ℝ n baseBump :=
  Complex.ofRealCLM.contDiff.comp contDiff_baseBumpReal

theorem baseBumpReal_nonneg (u : ℝ) : 0 ≤ baseBumpReal u :=
  div_nonneg baseContDiffBump.nonneg baseContDiffBump.integral_pos.le

theorem baseBumpReal_even (u : ℝ) : baseBumpReal (-u) = baseBumpReal u :=
  baseContDiffBump.normed_neg u

theorem baseBump_even (u : ℝ) : baseBump (-u) = baseBump u := by
  simp only [baseBump, baseBumpReal_even]

theorem integral_baseBumpReal : ∫ u : ℝ, baseBumpReal u = 1 :=
  baseContDiffBump.integral_normed

theorem baseBumpReal_eq_zero_of_abs_ge {u : ℝ} (hu : 1 / 4 ≤ |u|) : baseBumpReal u = 0 := by
  have hnot : u ∉ Function.support (baseContDiffBump.normed volume) := by
    rw [baseContDiffBump.support_normed_eq]
    simp only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, not_lt]
    exact hu
  exact Function.notMem_support.mp hnot

theorem baseBump_eq_zero_of_abs_ge {u : ℝ} (hu : 1 / 4 ≤ |u|) : baseBump u = 0 := by
  simp only [baseBump, baseBumpReal_eq_zero_of_abs_ge hu, Complex.ofReal_zero]

theorem tsupport_baseBumpReal_subset : tsupport baseBumpReal ⊆ Icc (-(1 / 4 : ℝ)) (1 / 4) := by
  refine closure_minimal (fun u hu => ?_) isClosed_Icc
  rw [mem_Icc, ← abs_le]
  by_contra h
  exact hu (baseBumpReal_eq_zero_of_abs_ge (not_le.mp h).le)

theorem hasCompactSupport_baseBumpReal : HasCompactSupport baseBumpReal :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    ((subset_tsupport baseBumpReal).trans tsupport_baseBumpReal_subset)

theorem tsupport_baseBump_subset : tsupport baseBump ⊆ Icc (-(1 / 4 : ℝ)) (1 / 4) := by
  refine closure_minimal (fun u hu => ?_) isClosed_Icc
  rw [mem_Icc, ← abs_le]
  by_contra h
  exact hu (baseBump_eq_zero_of_abs_ge (not_le.mp h).le)

theorem hasCompactSupport_baseBump : HasCompactSupport baseBump :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    ((subset_tsupport baseBump).trans tsupport_baseBump_subset)

/-- Twisted base bump `e^{-iγu} h(u)` packaged as a `CompactTest` for `heckeDefect`. -/
def baseTwistTest (γ : ℝ) : CompactTest :=
  ⟨twist γ baseBump, contDiff_twist contDiff_baseBump γ,
    hasCompactSupport_twist hasCompactSupport_baseBump γ⟩

/-- Primitive `H₀(x) = ∫_0^x h₀(v) dv` of `baseBumpReal`. -/
def baseBumpPrimitive (x : ℝ) : ℝ := ∫ v in (0 : ℝ)..x, baseBumpReal v

theorem hasDerivAt_baseBumpPrimitive (x : ℝ) :
    HasDerivAt baseBumpPrimitive (baseBumpReal x) x :=
  intervalIntegral.integral_hasDerivAt_right
    ((contDiff_baseBumpReal (n := ⊤)).continuous.intervalIntegrable _ _)
    ((contDiff_baseBumpReal (n := ⊤)).continuous.stronglyMeasurableAtFilter _ _)
    (contDiff_baseBumpReal (n := ⊤)).continuous.continuousAt

theorem deriv_baseBumpPrimitive : deriv baseBumpPrimitive = baseBumpReal :=
  funext fun x => (hasDerivAt_baseBumpPrimitive x).deriv

theorem contDiff_baseBumpPrimitive : ContDiff ℝ ∞ baseBumpPrimitive :=
  contDiff_infty_iff_deriv.mpr
    ⟨fun x => (hasDerivAt_baseBumpPrimitive x).differentiableAt, by
      rw [deriv_baseBumpPrimitive]; exact contDiff_baseBumpReal (n := ⊤)⟩

/-- Real continuous Hecke-averaged bump `F_L(u) = (2L)⁻¹ ∫_{u-L}^{u+L} h₀(v) dv`. -/
def heckeAvgReal (L u : ℝ) : ℝ :=
  (1 / (2 * L)) * ∫ v in (u - L)..(u + L), baseBumpReal v

/-- Complex continuous Hecke-averaged bump `F_L(u) = (heckeAvgReal L u : ℂ)`. -/
def heckeAvgBump (L u : ℝ) : ℂ := (heckeAvgReal L u : ℂ)

theorem heckeAvgReal_eq_primitive_sub (L u : ℝ) :
    heckeAvgReal L u =
      (1 / (2 * L)) * (baseBumpPrimitive (u + L) - baseBumpPrimitive (u - L)) := by
  unfold heckeAvgReal baseBumpPrimitive
  congr 1
  have h1 := intervalIntegral.integral_add_adjacent_intervals
    ((contDiff_baseBumpReal (n := ⊤)).continuous.intervalIntegrable (μ := volume) 0 (u - L))
    ((contDiff_baseBumpReal (n := ⊤)).continuous.intervalIntegrable (μ := volume) (u - L) (u + L))
  linarith

theorem heckeAvgReal_eq_shift_integral (L u : ℝ) :
    heckeAvgReal L u = (1 / (2 * L)) * ∫ l in (-L)..L, baseBumpReal (u - l) := by
  unfold heckeAvgReal
  congr 1
  have h := intervalIntegral.integral_comp_sub_left baseBumpReal u (a := -L) (b := L)
  rw [h]
  simp [sub_neg_eq_add]

theorem contDiff_heckeAvgReal (L : ℝ) : ContDiff ℝ ∞ (heckeAvgReal L) := by
  have heq : heckeAvgReal L = fun u =>
      (1 / (2 * L)) * (baseBumpPrimitive (u + L) - baseBumpPrimitive (u - L)) :=
    funext (heckeAvgReal_eq_primitive_sub L)
  rw [heq]
  exact contDiff_const.mul
    ((contDiff_baseBumpPrimitive.comp (contDiff_id.add contDiff_const)).sub
      (contDiff_baseBumpPrimitive.comp (contDiff_id.sub contDiff_const)))

theorem contDiff_heckeAvgBump (L : ℝ) : ContDiff ℝ 2 (heckeAvgBump L) :=
  Complex.ofRealCLM.contDiff.comp ((contDiff_infty.mp (contDiff_heckeAvgReal L)) 2)

theorem heckeAvgReal_even (L u : ℝ) : heckeAvgReal L (-u) = heckeAvgReal L u := by
  rw [heckeAvgReal_eq_shift_integral, heckeAvgReal_eq_shift_integral]
  congr 1
  have hneg := intervalIntegral.integral_comp_neg (fun l => baseBumpReal (u - l)) (a := -L) (b := L)
  rw [neg_neg] at hneg
  rw [← hneg]
  refine intervalIntegral.integral_congr fun l _ => ?_
  have : -u - l = -(u - -l) := by ring
  rw [this, baseBumpReal_even]

theorem heckeAvgBump_even (L u : ℝ) : heckeAvgBump L (-u) = heckeAvgBump L u := by
  simp only [heckeAvgBump, heckeAvgReal_even]

theorem heckeAvgReal_nonneg {L : ℝ} (hL : 0 < L) (u : ℝ) : 0 ≤ heckeAvgReal L u := by
  unfold heckeAvgReal
  refine mul_nonneg (by positivity) ?_
  exact intervalIntegral.integral_nonneg (by linarith) fun v _ => baseBumpReal_nonneg v

theorem heckeAvgReal_le {L : ℝ} (hL : 0 < L) (u : ℝ) : heckeAvgReal L u ≤ 1 / (2 * L) := by
  unfold heckeAvgReal
  have hint : Integrable baseBumpReal := baseContDiffBump.integrable_normed
  have hle : (∫ v in (u - L)..(u + L), baseBumpReal v) ≤ 1 := by
    rw [intervalIntegral.integral_of_le (by linarith), ← integral_baseBumpReal]
    exact setIntegral_le_integral hint (Eventually.of_forall baseBumpReal_nonneg)
  calc (1 / (2 * L)) * ∫ v in (u - L)..(u + L), baseBumpReal v
      ≤ (1 / (2 * L)) * 1 := mul_le_mul_of_nonneg_left hle (by positivity)
    _ = 1 / (2 * L) := mul_one _

theorem heckeAvgReal_eq_zero_of_abs_ge {L : ℝ} (hL : 0 < L) {u : ℝ} (hu : L + 1 / 4 ≤ |u|) :
    heckeAvgReal L u = 0 := by
  unfold heckeAvgReal
  rw [intervalIntegral.integral_of_le (by linarith)]
  suffices ∫ v in Ioc (u - L) (u + L), baseBumpReal v = 0 by rw [this, mul_zero]
  refine setIntegral_eq_zero_of_forall_eq_zero fun v hv => ?_
  apply baseBumpReal_eq_zero_of_abs_ge
  rw [mem_Ioc] at hv
  rcases le_or_gt 0 u with hu0 | hu0
  · rw [abs_of_nonneg hu0] at hu
    exact (by linarith : 1 / 4 ≤ v).trans (le_abs_self v)
  · rw [abs_of_neg hu0] at hu
    exact (by linarith : 1 / 4 ≤ -v).trans (neg_le_abs v)

theorem heckeAvgBump_eq_zero_of_abs_ge {L : ℝ} (hL : 0 < L) {u : ℝ} (hu : L + 1 / 4 ≤ |u|) :
    heckeAvgBump L u = 0 := by
  simp only [heckeAvgBump, heckeAvgReal_eq_zero_of_abs_ge hL hu, Complex.ofReal_zero]

theorem tsupport_heckeAvgReal_subset {L : ℝ} (hL : 0 < L) :
    tsupport (heckeAvgReal L) ⊆ Icc (-(L + 1 / 4)) (L + 1 / 4) := by
  refine closure_minimal (fun u hu => ?_) isClosed_Icc
  rw [mem_Icc, ← abs_le]
  by_contra h
  exact hu (heckeAvgReal_eq_zero_of_abs_ge hL (not_le.mp h).le)

theorem hasCompactSupport_heckeAvgReal {L : ℝ} (hL : 0 < L) :
    HasCompactSupport (heckeAvgReal L) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    ((subset_tsupport (heckeAvgReal L)).trans (tsupport_heckeAvgReal_subset hL))

theorem tsupport_heckeAvgBump_subset {L : ℝ} (hL : 0 < L) :
    tsupport (heckeAvgBump L) ⊆ Icc (-(L + 1 / 4)) (L + 1 / 4) := by
  refine closure_minimal (fun u hu => ?_) isClosed_Icc
  rw [mem_Icc, ← abs_le]
  by_contra h
  exact hu (heckeAvgBump_eq_zero_of_abs_ge hL (not_le.mp h).le)

theorem hasCompactSupport_heckeAvgBump {L : ℝ} (hL : 0 < L) :
    HasCompactSupport (heckeAvgBump L) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    ((subset_tsupport (heckeAvgBump L)).trans (tsupport_heckeAvgBump_subset hL))

/-- Second derivative of `heckeAvgReal L`: `F_L''(u) = (2L)⁻¹ (h₀'(u + L) − h₀'(u − L))`. -/
theorem deriv_deriv_heckeAvgReal (L u : ℝ) :
    deriv (deriv (heckeAvgReal L)) u =
      (1 / (2 * L)) * (deriv baseBumpReal (u + L) - deriv baseBumpReal (u - L)) := by
  have hdf : Differentiable ℝ baseBumpPrimitive := fun y =>
    (hasDerivAt_baseBumpPrimitive y).differentiableAt
  have hd1 : deriv (heckeAvgReal L) =
      fun x => (1 / (2 * L)) * (baseBumpReal (x + L) - baseBumpReal (x - L)) := by
    ext x
    have heq : heckeAvgReal L = fun y =>
        (1 / (2 * L)) * (baseBumpPrimitive (y + L) - baseBumpPrimitive (y - L)) :=
      funext (heckeAvgReal_eq_primitive_sub L)
    have hp1 : DifferentiableAt ℝ (fun y => baseBumpPrimitive (y + L)) x :=
      differentiableAt_comp_add_const.mpr (hdf (x + L))
    have hp2 : DifferentiableAt ℝ (fun y => baseBumpPrimitive (y - L)) x :=
      differentiableAt_comp_sub_const.mpr (hdf (x - L))
    have hp12 : DifferentiableAt ℝ
        (fun y => baseBumpPrimitive (y + L) - baseBumpPrimitive (y - L)) x :=
      hp1.sub hp2
    rw [heq, deriv_const_mul _ hp12, deriv_fun_sub hp1 hp2,
      deriv_comp_add_const, deriv_comp_sub_const, deriv_baseBumpPrimitive]
  have hdb : Differentiable ℝ baseBumpReal :=
    (contDiff_baseBumpReal (n := 1)).differentiable one_ne_zero
  have hb1 : DifferentiableAt ℝ (fun x => baseBumpReal (x + L)) u :=
    differentiableAt_comp_add_const.mpr (hdb (u + L))
  have hb2 : DifferentiableAt ℝ (fun x => baseBumpReal (x - L)) u :=
    differentiableAt_comp_sub_const.mpr (hdb (u - L))
  have hb12 : DifferentiableAt ℝ (fun x => baseBumpReal (x + L) - baseBumpReal (x - L)) u :=
    hb1.sub hb2
  rw [hd1, deriv_const_mul _ hb12, deriv_fun_sub hb1 hb2,
    deriv_comp_add_const, deriv_comp_sub_const]

theorem deriv_deriv_heckeAvgBump (L u : ℝ) :
    deriv (deriv (heckeAvgBump L)) u = ((deriv (deriv (heckeAvgReal L)) u : ℝ) : ℂ) := by
  have hcd3 : ContDiff ℝ 3 (heckeAvgReal L) := (contDiff_infty.mp (contDiff_heckeAvgReal L)) 3
  have hcd2 : ContDiff ℝ 2 (deriv (heckeAvgReal L)) :=
    (contDiff_succ_iff_deriv.mp hcd3).2.2
  have h1 : deriv (heckeAvgBump L) = fun x => ((deriv (heckeAvgReal L) x : ℝ) : ℂ) := by
    ext x
    exact (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt x
      (hcd3.differentiable (by norm_num) x).hasDerivAt).deriv
  rw [h1]
  exact (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt u
    (hcd2.differentiable (by norm_num) u).hasDerivAt).deriv

/-- Whole-line integral of a function vanishing on `|u| ≥ A` (`A > 0`) equals its interval integral
on `(-A)..A`. -/
private theorem integral_eq_intervalIntegral_of_eq_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {g : ℝ → E} {A : ℝ} (hA : 0 < A)
    (hsupp : ∀ u, A ≤ |u| → g u = 0) :
    ∫ u : ℝ, g u = ∫ u in (-A)..A, g u := by
  rw [intervalIntegral.integral_of_le (by linarith)]
  refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun u hu => ?_).symm
  apply hsupp
  rw [mem_Ioc, not_and_or, not_lt, not_le] at hu
  rcases hu with hu | hu
  · exact (by linarith : A ≤ -u).trans (neg_le_abs u)
  · exact hu.le.trans (le_abs_self u)

/-- Unit mass of `heckeAvgReal L` for `L > 0`. -/
theorem integral_heckeAvgReal {L : ℝ} (hL : 0 < L) : ∫ u : ℝ, heckeAvgReal L u = 1 := by
  rw [integral_eq_intervalIntegral_of_eq_zero (A := L + 1) (by positivity)
    (fun u hu => heckeAvgReal_eq_zero_of_abs_ge hL (by linarith))]
  simp_rw [heckeAvgReal_eq_shift_integral]
  rw [intervalIntegral.integral_const_mul]
  have hcont : Continuous (Function.uncurry fun u l : ℝ => baseBumpReal (u - l)) :=
    (contDiff_baseBumpReal (n := ⊤)).continuous.comp (continuous_fst.sub continuous_snd)
  have hint : IntegrableOn (Function.uncurry fun u l : ℝ => baseBumpReal (u - l))
      (uIoc (-(L + 1)) (L + 1) ×ˢ uIoc (-L) L) :=
    (hcont.continuousOn.integrableOn_compact
      (isCompact_uIcc.prod isCompact_uIcc)).mono_set
      (prod_mono uIoc_subset_uIcc uIoc_subset_uIcc)
  rw [intervalIntegral_intervalIntegral_swap hint]
  have Dinner : ∀ l ∈ uIcc (-L) L,
      ∫ u in (-(L + 1))..(L + 1), baseBumpReal (u - l) = 1 := by
    intro l hl
    rw [uIcc_of_le (by linarith)] at hl
    rw [← integral_eq_intervalIntegral_of_eq_zero (A := L + 1) (by positivity)]
    · rw [integral_sub_right_eq_self, integral_baseBumpReal]
    · intro u hu
      apply baseBumpReal_eq_zero_of_abs_ge
      rcases le_or_gt 0 u with hu0 | hu0
      · rw [abs_of_nonneg hu0] at hu
        exact (by linarith [hl.2] : 1 / 4 ≤ u - l).trans (le_abs_self _)
      · rw [abs_of_neg hu0] at hu
        exact (by linarith [hl.1] : 1 / 4 ≤ -(u - l)).trans (neg_le_abs _)
  rw [intervalIntegral.integral_congr Dinner, intervalIntegral.integral_const, smul_eq_mul,
    mul_one, sub_neg_eq_add]
  field_simp; ring

theorem integral_norm_heckeAvgBump {L : ℝ} (hL : 0 < L) :
    ∫ u : ℝ, ‖heckeAvgBump L u‖ = 1 := by
  have heq : (fun u => ‖heckeAvgBump L u‖) = heckeAvgReal L := by
    ext u
    rw [heckeAvgBump, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (heckeAvgReal_nonneg hL u)]
  rw [heq, integral_heckeAvgReal hL]

theorem integral_norm_sq_heckeAvgBump_le {L : ℝ} (hL : 0 < L) :
    ∫ u : ℝ, ‖heckeAvgBump L u‖ ^ 2 ≤ 1 / (2 * L) := by
  have hint1 : Integrable (heckeAvgReal L) :=
    ((contDiff_heckeAvgReal L).continuous).integrable_of_hasCompactSupport
      (hasCompactSupport_heckeAvgReal hL)
  have hcs2 : HasCompactSupport (fun u => ‖heckeAvgBump L u‖ ^ 2) := by
    refine HasCompactSupport.of_support_subset_isCompact (K := Icc (-(L + 1 / 4)) (L + 1 / 4))
      isCompact_Icc fun u hu => ?_
    rw [mem_Icc, ← abs_le]
    by_contra h
    exact hu (by simp [heckeAvgBump_eq_zero_of_abs_ge hL (not_le.mp h).le])
  have hint2 : Integrable (fun u => ‖heckeAvgBump L u‖ ^ 2) :=
    ((contDiff_heckeAvgBump L).continuous.norm.pow 2).integrable_of_hasCompactSupport hcs2
  calc ∫ u : ℝ, ‖heckeAvgBump L u‖ ^ 2
      ≤ ∫ u : ℝ, (1 / (2 * L)) * heckeAvgReal L u := by
        refine integral_mono hint2 (hint1.const_mul _) fun u => ?_
        dsimp only
        have h0 := heckeAvgReal_nonneg hL u
        have hle := heckeAvgReal_le hL u
        have hn : ‖heckeAvgBump L u‖ = heckeAvgReal L u := by
          rw [heckeAvgBump, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]
        rw [hn]
        nlinarith
    _ = (1 / (2 * L)) * ∫ u : ℝ, heckeAvgReal L u := integral_const_mul _ _
    _ = 1 / (2 * L) := by rw [integral_heckeAvgReal hL, mul_one]

/-- Scale-uniform `C²` envelope bound for `heckeAvgBump L` across all `L ≥ 1`. -/
def heckeAvgEnvelopeCap : ℝ :=
  4 * (1 + ∫ u : ℝ, |deriv baseBumpReal u|)

theorem envelope_heckeAvgBump_le {L : ℝ} (hL : 1 ≤ L) :
    envelope (heckeAvgBump L) ≤ heckeAvgEnvelopeCap := by
  have hLpos : 0 < L := lt_of_lt_of_le one_pos hL
  unfold envelope heckeAvgEnvelopeCap
  rw [integral_norm_heckeAvgBump hLpos]
  have hcd1 : ContDiff ℝ 1 baseBumpReal := contDiff_baseBumpReal (n := 1)
  have hcont_d : Continuous (fun u => |deriv baseBumpReal u|) :=
    (hcd1.continuous_deriv le_rfl).abs
  have hc_d : HasCompactSupport (deriv baseBumpReal) :=
    hasCompactSupport_baseBumpReal.deriv
  have hint_d : Integrable (fun u => |deriv baseBumpReal u|) :=
    hcont_d.integrable_of_hasCompactSupport hc_d.abs
  have hint_dd : Integrable (fun u => ‖deriv (deriv (heckeAvgBump L)) u‖) := by
    have hcd2 := contDiff_heckeAvgBump L
    have hcont2 : Continuous (deriv (deriv (heckeAvgBump L))) := by
      have hd1 : ContDiff ℝ 1 (deriv (heckeAvgBump L)) :=
        (contDiff_succ_iff_deriv.mp hcd2).2.2
      exact hd1.continuous_deriv le_rfl
    exact hcont2.norm.integrable_of_hasCompactSupport
      (hasCompactSupport_heckeAvgBump hLpos).deriv.deriv.norm
  have hle_dd : ∫ u : ℝ, ‖deriv (deriv (heckeAvgBump L)) u‖ ≤
      ∫ u : ℝ, |deriv baseBumpReal u| := by
    have hbound : ∫ u : ℝ, ‖deriv (deriv (heckeAvgBump L)) u‖ ≤
        ∫ u : ℝ, (1 / (2 * L)) * (|deriv baseBumpReal (u + L)| + |deriv baseBumpReal (u - L)|) := by
      refine integral_mono hint_dd
        (((hint_d.comp_add_right L).add (hint_d.comp_sub_right L)).const_mul _) fun u => ?_
      dsimp only
      rw [deriv_deriv_heckeAvgBump, Complex.norm_real, Real.norm_eq_abs, deriv_deriv_heckeAvgReal,
        abs_mul, abs_of_pos (by positivity)]
      exact mul_le_mul_of_nonneg_left (abs_sub _ _) (by positivity)
    rw [integral_const_mul, integral_add (hint_d.comp_add_right L) (hint_d.comp_sub_right L),
      integral_add_right_eq_self (fun u => |deriv baseBumpReal u|) L,
      integral_sub_right_eq_self (fun u => |deriv baseBumpReal u|) L] at hbound
    have hnn : 0 ≤ ∫ u : ℝ, |deriv baseBumpReal u| := integral_nonneg fun _ => abs_nonneg _
    have hdiv : (1 / (2 * L)) * ((∫ u : ℝ, |deriv baseBumpReal u|) + ∫ u : ℝ, |deriv baseBumpReal u|) =
        (∫ u : ℝ, |deriv baseBumpReal u|) / L := by field_simp; ring
    rw [hdiv] at hbound
    exact hbound.trans (div_le_self hnn hL)
  linarith

/-! ## §3. Hyperbolic `cosh` fibre coercivity and `H(γ) ≤ D(twist γ F_L)` -/

/-- For a real, even, nonnegative, integrable, unit-mass profile `f`, at any point `ρ : ℂ` on the
horizontal line `Im ρ = γ` the twisted transform is real and at least `1` via `cosh(δ u) ≥ 1`. -/
theorem one_le_re_tr_twist_of_im_eq {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (heven : ∀ u, f (-u) = f u) (hnn : ∀ u, 0 ≤ f u) (hmass : ∫ u : ℝ, f u = 1)
    {γ : ℝ} {ρ : ℂ} (him : ρ.im = γ) :
    1 ≤ (tr (twist γ (fun u => (f u : ℂ))) ρ).re := by
  rw [tr_twist, tr_eq]
  set δ := ρ.re - 1 / 2
  have hexp : ∀ u : ℝ, (ρ - (γ : ℂ) * I - 1 / 2) * (u : ℂ) = ((δ * u : ℝ) : ℂ) := by
    intro u
    apply Complex.ext
    · simp [δ]
    · simp [him]
  have hint_exp : Integrable (fun u : ℝ => f u * Real.exp (δ * u)) :=
    (hf.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))).integrable_of_hasCompactSupport
      (hfc.mul_right)
  have hint_f : Integrable f := hf.integrable_of_hasCompactSupport hfc
  have htr : (∫ u : ℝ, (f u : ℂ) * Complex.exp ((ρ - (γ : ℂ) * I - 1 / 2) * (u : ℂ))).re =
      ∫ u : ℝ, f u * Real.exp (δ * u) := by
    have hfun : (fun u : ℝ => (f u : ℂ) * Complex.exp ((ρ - (γ : ℂ) * I - 1 / 2) * (u : ℂ))) =
        fun u : ℝ => ((f u * Real.exp (δ * u) : ℝ) : ℂ) := by
      ext u
      rw [hexp u, ← Complex.ofReal_exp, Complex.ofReal_mul]
    rw [hfun, integral_complex_ofReal, Complex.ofReal_re]
  rw [htr]
  have hneg : ∫ u : ℝ, f u * Real.exp (-(δ * u)) = ∫ u : ℝ, f u * Real.exp (δ * u) := by
    rw [← integral_neg_eq_self]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [heven, mul_neg, neg_neg]
  have hcosh : ∫ u : ℝ, f u * Real.cosh (δ * u) = ∫ u : ℝ, f u * Real.exp (δ * u) := by
    have hfun : (fun u : ℝ => f u * Real.cosh (δ * u)) =
        fun u => (1 / 2 : ℝ) * (f u * Real.exp (δ * u) + f u * Real.exp (-(δ * u))) := by
      ext u; rw [Real.cosh_eq]; ring
    have hint_n : Integrable (fun u : ℝ => f u * Real.exp (-(δ * u))) := by
      have := hint_exp.comp_neg
      refine this.congr (Eventually.of_forall fun u => ?_)
      simp [heven, mul_neg]
    rw [hfun, integral_const_mul, integral_add hint_exp hint_n, hneg]
    ring
  rw [← hcosh, ← hmass]
  refine integral_mono hint_f
    ((hf.mul (Real.continuous_cosh.comp (continuous_const.mul continuous_id))).integrable_of_hasCompactSupport
      hfc.mul_right) fun u => ?_
  dsimp only
  exact le_mul_of_one_le_right (hnn u) (Real.one_le_cosh _)

/-- **Horizontal fibre coercivity.** For every `L > 0` and every ordinate `γ ∈ ℝ`,
`H(γ) ≤ D(twist γ F_L)`. -/
theorem horizontalMultiplicity_le_collidedForm_heckeAvg {L : ℝ} (hL : 0 < L) (γ : ℝ) :
    (xiHorizontalMultiplicity γ : ℝ) ≤ collidedForm zetaZeroConfig (twist γ (heckeAvgBump L)) := by
  classical
  have hs := zeta_summable_collided (contDiff_twist (contDiff_heckeAvgBump L) γ)
    (hasCompactSupport_twist (hasCompactSupport_heckeAvgBump hL) γ)
  -- Map `stripHeightFinset γ` injectively into `zetaZeroConfig.carrier`
  have hmem_c : ∀ z ∈ stripHeightFinset γ, z ∈ zetaZeroConfig.carrier := by
    intro z hz
    obtain ⟨h0, h1, _, hxi⟩ := mem_stripHeightFinset.mp hz
    exact CrossRouteReceiverBridges.mem_zetaZeroConfig_carrier_iff_xi_eq_zero_and_strip.mpr
      ⟨hxi, h0, h1⟩
  let emb : {z // z ∈ stripHeightFinset γ} → zetaZeroConfig.carrier :=
    fun z => ⟨z.1, hmem_c z.1 z.2⟩
  have hinj : Function.Injective emb := fun a b h =>
    Subtype.ext (congrArg (fun x : zetaZeroConfig.carrier => (x : ℂ)) h)
  let S : Finset zetaZeroConfig.carrier := (stripHeightFinset γ).attach.image emb
  have hfib_sum : (xiHorizontalMultiplicity γ : ℝ) ≤
      ∑ ρ ∈ S, (zetaZeroConfig.mult ρ : ℝ) * Complex.normSq (tr (twist γ (heckeAvgBump L)) ρ) := by
    rw [xiHorizontalMultiplicity, Nat.cast_sum,
      ← Finset.sum_attach (stripHeightFinset γ) (fun z => ((analyticOrderAt xi z).toNat : ℝ)),
      Finset.sum_image (fun a _ b _ h => hinj h)]
    refine Finset.sum_le_sum fun z _ => ?_
    obtain ⟨h0, h1, hzim, _⟩ := mem_stripHeightFinset.mp z.2
    have hmult : (analyticOrderAt xi z.1).toNat = zetaZeroConfig.mult (emb z) := by
      change (analyticOrderAt xi z.1).toNat = (analyticOrderAt riemannZeta z.1).toNat
      rw [xi_analyticOrderAt_eq_riemannZeta_of_mem_strip ⟨h0, h1⟩]
    rw [hmult]
    have h1le := one_le_re_tr_twist_of_im_eq ((contDiff_heckeAvgReal L).continuous)
      (hasCompactSupport_heckeAvgReal hL) (heckeAvgReal_even L) (heckeAvgReal_nonneg hL)
      (integral_heckeAvgReal hL) hzim
    have hnsq : 1 ≤ Complex.normSq (tr (twist γ (heckeAvgBump L)) (emb z)) := by
      rw [Complex.normSq_apply]
      have hre : 1 ≤ (tr (twist γ (heckeAvgBump L)) z.1).re := h1le
      change 1 ≤ (tr (twist γ (heckeAvgBump L)) z.1).re * (tr (twist γ (heckeAvgBump L)) z.1).re + _
      nlinarith [sq_nonneg (tr (twist γ (heckeAvgBump L)) z.1).im]
    exact le_mul_of_one_le_right (Nat.cast_nonneg _) hnsq
  exact hfib_sum.trans
    (hs.sum_le_tsum S fun ρ _ => mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _))

/-! ## §4. Fubini transform factorization and sinc-cancelled off-line defect bound -/

/-- Exact Fubini factorization of `tr (twist γ F_L) s`: the continuous Hecke average multiplies
`tr (twist γ baseBump) s` by `(2L)⁻¹ ∫_{-L}^L e^{(s − 1/2 − iγ)ℓ} dℓ`. -/
theorem tr_twist_heckeAvgBump_eq {L : ℝ} (hL : 0 < L) (γ : ℝ) (s : ℂ) :
    tr (twist γ (heckeAvgBump L)) s =
      ((1 / (2 * L) : ℝ) : ℂ) *
        (∫ l in (-L)..L, Complex.exp ((s - 1 / 2 - (γ : ℂ) * I) * (l : ℂ)) *
          tr (twist γ baseBump) s) := by
  rw [tr_twist, tr_eq, integral_eq_intervalIntegral_of_eq_zero (A := L + 1) (by positivity)]
  · have hrew : ∀ u : ℝ, heckeAvgBump L u * Complex.exp ((s - (γ : ℂ) * I - 1 / 2) * (u : ℂ)) =
        ((1 / (2 * L) : ℝ) : ℂ) * ∫ l in (-L)..L,
          baseBump (u - l) * Complex.exp ((s - 1 / 2 - (γ : ℂ) * I) * (u : ℂ)) := by
      intro u
      rw [heckeAvgBump, heckeAvgReal_eq_shift_integral, Complex.ofReal_mul, mul_assoc]
      congr 1
      have hsub : s - (γ : ℂ) * I - 1 / 2 = s - 1 / 2 - (γ : ℂ) * I := by ring
      rw [hsub, ← intervalIntegral.integral_ofReal, ← intervalIntegral.integral_mul_const]
      rfl
    simp_rw [hrew]
    rw [intervalIntegral.integral_const_mul]
    congr 1
    have hcont : Continuous (Function.uncurry fun u l : ℝ =>
        baseBump (u - l) * Complex.exp ((s - 1 / 2 - (γ : ℂ) * I) * (u : ℂ))) :=
      ((contDiff_baseBump (n := ⊤)).continuous.comp (continuous_fst.sub continuous_snd)).mul
        (Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp continuous_fst)))
    have hint : IntegrableOn (Function.uncurry fun u l : ℝ =>
        baseBump (u - l) * Complex.exp ((s - 1 / 2 - (γ : ℂ) * I) * (u : ℂ)))
        (uIoc (-(L + 1)) (L + 1) ×ˢ uIoc (-L) L) :=
      (hcont.continuousOn.integrableOn_compact
        (isCompact_uIcc.prod isCompact_uIcc)).mono_set
        (prod_mono uIoc_subset_uIcc uIoc_subset_uIcc)
    rw [intervalIntegral_intervalIntegral_swap hint]
    refine intervalIntegral.integral_congr fun l hl => ?_
    rw [uIcc_of_le (by linarith)] at hl
    rw [← integral_eq_intervalIntegral_of_eq_zero (A := L + 1) (by positivity)]
    · -- Shift `u ↦ u + l`
      rw [← integral_add_right_eq_self (fun u : ℝ =>
        baseBump (u - l) * Complex.exp ((s - 1 / 2 - (γ : ℂ) * I) * (u : ℂ))) l]
      have hfun : (fun u : ℝ =>
          baseBump (u + l - l) * Complex.exp ((s - 1 / 2 - (γ : ℂ) * I) * ((u + l : ℝ) : ℂ))) =
          fun u : ℝ => Complex.exp ((s - 1 / 2 - (γ : ℂ) * I) * (l : ℂ)) *
            (baseBump u * Complex.exp ((s - (γ : ℂ) * I - 1 / 2) * (u : ℂ))) := by
        ext u
        simp only [add_sub_cancel_right]
        push_cast
        rw [show (s - 1 / 2 - (γ : ℂ) * I) * ((u : ℂ) + (l : ℂ)) =
          (s - 1 / 2 - (γ : ℂ) * I) * (l : ℂ) + (s - (γ : ℂ) * I - 1 / 2) * (u : ℂ) by ring,
          Complex.exp_add]
        ring
      rw [hfun, integral_const_mul, ← tr_eq, ← tr_twist]
    · intro u hu
      have hb0 : baseBump (u - l) = 0 := by
        apply baseBump_eq_zero_of_abs_ge
        rcases le_or_gt 0 u with hu0 | hu0
        · rw [abs_of_nonneg hu0] at hu
          exact (by linarith [hl.2] : 1 / 4 ≤ u - l).trans (le_abs_self _)
        · rw [abs_of_neg hu0] at hu
          exact (by linarith [hl.1] : 1 / 4 ≤ -(u - l)).trans (neg_le_abs _)
      rw [hb0, zero_mul]
  · intro u hu
    rw [heckeAvgBump_eq_zero_of_abs_ge hL (by linarith), zero_mul]

/-- Universal real inequality `(e^x − 1)² ≤ depthKernel 1 x = (e^x − e^{−x})²`. -/
private theorem sq_exp_sub_one_le_depthKernel_one (x : ℝ) :
    (Real.exp x - 1) ^ 2 ≤ depthKernel 1 x := by
  have hdk : depthKernel 1 x = (Real.exp x - Real.exp (-x)) ^ 2 := by
    rw [depthKernel_eq_four_sinh_sq, mul_one, Real.sinh_eq]
    ring
  rw [hdk, sq_le_sq]
  rcases le_or_gt 0 x with hx | hx
  · have h1 : 0 ≤ Real.exp x - 1 := sub_nonneg.mpr (Real.one_le_exp hx)
    have h2 : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    rw [abs_of_nonneg h1, abs_of_nonneg (by linarith)]
    linarith
  · have h1 : Real.exp x ≤ 1 := Real.exp_le_one_iff.mpr hx.le
    have h2 : 1 ≤ Real.exp (-x) := Real.one_le_exp (by linarith)
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    linarith

/-- For `|l| ≤ L` (`L > 0`), `(e^{δ l} − 1)² ≤ depthKernel L δ`. -/
private theorem sq_exp_mul_sub_one_le_depthKernel {L δ l : ℝ} (hL : 0 < L) (hl : |l| ≤ L) :
    (Real.exp (δ * l) - 1) ^ 2 ≤ depthKernel L δ := by
  have h1 := sq_exp_sub_one_le_depthKernel_one (δ * l)
  have h2 : depthKernel 1 (δ * l) = depthKernel δ l := by
    unfold depthKernel; ring_nf
  have h3 : depthKernel δ l ≤ depthKernel δ L := by
    rw [depthKernel_le_iff, abs_mul, abs_mul, abs_of_pos hL]
    exact mul_le_mul_of_nonneg_right hl (abs_nonneg δ)
  have h4 : depthKernel δ L = depthKernel L δ := by
    unfold depthKernel; ring_nf
  exact h1.trans (h2.le.trans (h3.trans_eq h4))

/-- Norm bound `‖e^{iθ} − 1‖ ≤ |θ|` for real `θ`. -/
private theorem norm_exp_I_mul_ofReal_sub_one_le (θ : ℝ) :
    ‖Complex.exp (I * (θ : ℂ)) - 1‖ ≤ |θ| := by
  have hsq : ‖Complex.exp (I * (θ : ℂ)) - 1‖ ^ 2 ≤ |θ| ^ 2 := by
    rw [mul_comm I, Complex.exp_mul_I, Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.add_re, Complex.cos_ofReal_re, Complex.mul_re,
      Complex.sin_ofReal_re, Complex.I_re, mul_zero, Complex.sin_ofReal_im, Complex.I_im,
      mul_one, sub_zero, add_zero, Complex.one_re, Complex.sub_im, Complex.add_im,
      Complex.cos_ofReal_im, Complex.mul_im, zero_add, Complex.one_im]
    have htrig : (Real.cos θ - 1) * (Real.cos θ - 1) + Real.sin θ * Real.sin θ =
        4 * Real.sin (θ / 2) ^ 2 := by
      have hc := Real.cos_two_mul (θ / 2)
      rw [show 2 * (θ / 2) = θ by ring] at hc
      have hs := Real.sin_sq_add_cos_sq (θ / 2)
      have hs0 := Real.sin_sq_add_cos_sq θ
      nlinarith
    rw [htrig]
    have hsin : |Real.sin (θ / 2)| ≤ |θ / 2| := Real.abs_sin_le_abs
    have hsin2 : Real.sin (θ / 2) ^ 2 ≤ (θ / 2) ^ 2 := by
      rw [← sq_abs, ← sq_abs (θ / 2)]
      exact pow_le_pow_left₀ (abs_nonneg _) hsin 2
    rw [sq_abs]
    linarith
  exact ( abs_le_of_sq_le_sq' hsq (abs_nonneg θ) ).2

/-- Near-frequency Lipschitz cancellation of the base bump reflection mismatch: since `baseBump` is
real and even on `[-1/4, 1/4]`, `‖u_ρ − v_ρ‖ ≤ |Im ρ − γ|` for every nontrivial zero `ρ`. -/
private theorem norm_tr_twist_baseBump_sub_refl_le (γ : ℝ) (ρ : zetaZeroConfig.carrier) :
    ‖tr (twist γ baseBump) ρ - tr (twist γ baseBump) (rosatiRefl ρ)‖ ≤ |(ρ : ℂ).im - γ| := by
  set δ := (ρ : ℂ).re - 1 / 2
  set dω := (ρ : ℂ).im - γ
  have hstrip := zetaZeroConfig.strip ρ ρ.2
  have hδ : |δ| ≤ 1 / 2 := by
    rw [abs_le]; constructor <;> simp only [δ] <;> linarith [hstrip.1, hstrip.2]
  rw [tr_twist, tr_twist, tr_eq, tr_eq]
  have hexp1 : ∀ x : ℝ, ((ρ : ℂ) - (γ : ℂ) * I - 1 / 2) * (x : ℂ) =
      ((δ * x : ℝ) : ℂ) + I * ((dω * x : ℝ) : ℂ) := by
    intro x
    apply Complex.ext
    · simp [δ, dω]
    · simp [δ, dω]
  have hexp2 : ∀ x : ℝ, (rosatiRefl (ρ : ℂ) - (γ : ℂ) * I - 1 / 2) * (x : ℂ) =
      ((-(δ * x) : ℝ) : ℂ) + I * ((dω * x : ℝ) : ℂ) := by
    intro x
    apply Complex.ext
    · simp [rosatiRefl, δ, dω]; ring
    · simp [rosatiRefl, δ, dω]
  have hint1 : Integrable (fun x : ℝ =>
      baseBump x * Complex.exp (((ρ : ℂ) - (γ : ℂ) * I - 1 / 2) * (x : ℂ))) :=
    ((contDiff_baseBump (n := ⊤)).continuous.mul
      (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))).integrable_of_hasCompactSupport
      hasCompactSupport_baseBump.mul_right
  have hint2 : Integrable (fun x : ℝ =>
      baseBump x * Complex.exp ((rosatiRefl (ρ : ℂ) - (γ : ℂ) * I - 1 / 2) * (x : ℂ))) :=
    ((contDiff_baseBump (n := ⊤)).continuous.mul
      (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))).integrable_of_hasCompactSupport
      hasCompactSupport_baseBump.mul_right
  rw [← integral_sub hint1 hint2]
  -- Oddness of `h₀(x) (e^{δ x} − e^{−δ x})` kills the `dω = 0` term
  have hodd0 : ∫ x : ℝ, (baseBumpReal x : ℂ) *
      (((Real.exp (δ * x) - Real.exp (-(δ * x)) : ℝ) : ℂ)) = 0 := by
    have hreal : (∫ x : ℝ, (baseBumpReal x : ℂ) *
        (((Real.exp (δ * x) - Real.exp (-(δ * x)) : ℝ) : ℂ))) =
        ((∫ x : ℝ, baseBumpReal x * (Real.exp (δ * x) - Real.exp (-(δ * x))) : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      congr 1; ext x; push_cast; rfl
    rw [hreal, Complex.ofReal_eq_zero]
    set g : ℝ → ℝ := fun x => baseBumpReal x * (Real.exp (δ * x) - Real.exp (-(δ * x)))
    have hneg : ∫ x : ℝ, g (-x) = ∫ x : ℝ, g x := integral_neg_eq_self g volume
    have hanti : ∀ x : ℝ, g (-x) = -g x := by
      intro x; simp only [g, baseBumpReal_even, mul_neg, neg_neg]; ring
    simp_rw [hanti] at hneg
    rw [integral_neg] at hneg
    linarith
  have hint0 : Integrable (fun x : ℝ => (baseBumpReal x : ℂ) *
      (((Real.exp (δ * x) - Real.exp (-(δ * x)) : ℝ) : ℂ))) :=
    (Complex.continuous_ofReal.comp (contDiff_baseBumpReal (n := ⊤)).continuous |>.mul
      (Complex.continuous_ofReal.comp ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).sub
        (Real.continuous_exp.comp (continuous_neg.comp (continuous_const.mul continuous_id)))))).integrable_of_hasCompactSupport
      hasCompactSupport_baseBump.mul_right
  have hsub0 : (∫ x : ℝ, (baseBump x * Complex.exp (((ρ : ℂ) - (γ : ℂ) * I - 1 / 2) * (x : ℂ)) -
      baseBump x * Complex.exp ((rosatiRefl (ρ : ℂ) - (γ : ℂ) * I - 1 / 2) * (x : ℂ)))) =
      ∫ x : ℝ, (baseBumpReal x : ℂ) * (Complex.exp (I * ((dω * x : ℝ) : ℂ)) - 1) *
        (((Real.exp (δ * x) - Real.exp (-(δ * x)) : ℝ) : ℂ)) := by
    have hint12 : Integrable (fun x : ℝ =>
        baseBump x * Complex.exp (((ρ : ℂ) - (γ : ℂ) * I - 1 / 2) * (x : ℂ)) -
          baseBump x * Complex.exp ((rosatiRefl (ρ : ℂ) - (γ : ℂ) * I - 1 / 2) * (x : ℂ))) :=
      hint1.sub hint2
    rw [← sub_zero (∫ x : ℝ, _ - _), ← hodd0, ← integral_sub hint12 hint0]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    dsimp only [baseBump]
    rw [hexp1 x, hexp2 x, Complex.exp_add, Complex.exp_add, ← Complex.ofReal_exp,
      ← Complex.ofReal_exp, Complex.ofReal_sub]
    ring
  rw [hsub0]
  refine (norm_integral_le_integral_norm _).trans ?_
  rw [← mul_one |dω|, ← integral_baseBumpReal, ← integral_const_mul]
  refine integral_mono
    (((Complex.continuous_ofReal.comp (contDiff_baseBumpReal (n := ⊤)).continuous |>.mul
      ((Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
        (continuous_const.mul continuous_id)))).sub continuous_const)).mul
      (Complex.continuous_ofReal.comp ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).sub
        (Real.continuous_exp.comp (continuous_neg.comp (continuous_const.mul continuous_id)))))).norm.integrable_of_hasCompactSupport
      hasCompactSupport_baseBump.mul_right.mul_right.norm)
    (baseContDiffBump.integrable_normed.const_mul |dω|) fun x => ?_
  dsimp only
  by_cases hx : 1 / 4 ≤ |x|
  · rw [baseBumpReal_eq_zero_of_abs_ge hx]
    simp
  · push Not at hx
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (baseBumpReal_nonneg x), Complex.norm_real, Real.norm_eq_abs]
    have h1 := norm_exp_I_mul_ofReal_sub_one_le (dω * x)
    rw [abs_mul] at h1
    have h1' : ‖Complex.exp (I * ((dω * x : ℝ) : ℂ)) - 1‖ ≤ |dω| * (1 / 4) :=
      h1.trans (mul_le_mul_of_nonneg_left hx.le (abs_nonneg dω))
    have hexp_le : |Real.exp (δ * x) - Real.exp (-(δ * x))| ≤ 4 := by
      refine (abs_sub _ _).trans ?_
      rw [abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
      have hδx8 : |δ * x| ≤ Real.log 2 := by
        rw [abs_mul]
        have hl2 : (1 / 8 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
        nlinarith [abs_nonneg δ, abs_nonneg x]
      have hb1 : Real.exp (δ * x) ≤ 2 := by
        rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
        exact Real.exp_le_exp.mpr (abs_le.mp hδx8).2
      have hb2 : Real.exp (-(δ * x)) ≤ 2 := by
        rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
        exact Real.exp_le_exp.mpr (by linarith [(abs_le.mp hδx8).1])
      linarith
    have hb0 := baseBumpReal_nonneg x
    calc baseBumpReal x * ‖Complex.exp (I * ((dω * x : ℝ) : ℂ)) - 1‖ *
          |Real.exp (δ * x) - Real.exp (-(δ * x))|
        ≤ baseBumpReal x * (|dω| * (1 / 4)) * 4 := by
          gcongr
      _ = |dω| * baseBumpReal x := by ring

/-- Sinc bound on `[-L, L]`: for `L > 0` and `dω ≠ 0`,
`‖(2L)⁻¹ ∫_{-L}^L e^{i dω ℓ} dℓ‖ ≤ 1 / (L |dω|)`. -/
private theorem norm_sinc_intervalIntegral_le {L dω : ℝ} (hL : 0 < L) (hdω : dω ≠ 0) :
    ‖((1 / (2 * L) : ℝ) : ℂ) * ∫ l in (-L)..L, Complex.exp (I * (dω : ℂ) * (l : ℂ))‖ ≤
      1 / (L * |dω|) := by
  have hc : I * (dω : ℂ) ≠ 0 := mul_ne_zero I_ne_zero (Complex.ofReal_ne_zero.mpr hdω)
  rw [integral_exp_mul_complex hc, norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < 1 / (2 * L)), norm_mul, Complex.norm_I, one_mul,
    Complex.norm_real, Real.norm_eq_abs]
  have hn1 : ‖Complex.exp (I * (dω : ℂ) * (L : ℂ))‖ = 1 := by
    rw [show I * (dω : ℂ) * (L : ℂ) = ((dω * L : ℝ) : ℂ) * I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hn2 : ‖Complex.exp (I * (dω : ℂ) * ((-L : ℝ) : ℂ))‖ = 1 := by
    rw [show I * (dω : ℂ) * ((-L : ℝ) : ℂ) = ((dω * (-L) : ℝ) : ℂ) * I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hnum : ‖Complex.exp (I * (dω : ℂ) * (L : ℂ)) - Complex.exp (I * (dω : ℂ) * ((-L : ℝ) : ℂ))‖ ≤ 2 :=
    (norm_sub_le _ _).trans (by rw [hn1, hn2]; norm_num)
  calc 1 / (2 * L) *
        (‖Complex.exp (I * (dω : ℂ) * (L : ℂ)) - Complex.exp (I * (dω : ℂ) * ((-L : ℝ) : ℂ))‖ / |dω|)
      ≤ 1 / (2 * L) * (2 / |dω|) := by gcongr
    _ = 1 / (L * |dω|) := by field_simp

/-- Explicit constant in the sinc-cancelled Lorentzian tail of `offLineDefect`. -/
def sincLorentzConst : ℝ :=
  8 * (|xiLineTwoLogDerivConstant| + 1) * max 2 (4 * Real.exp (1 / 4) * envelope baseBump ^ 2)

theorem sincLorentzConst_pos : 0 < sincLorentzConst := by
  unfold sincLorentzConst
  positivity

/-- Averaged oscillatory factor `(2L)⁻¹ ∫_{-L}^L e^{i dω ℓ} dℓ`. -/
private def sincFactor (L dω : ℝ) : ℂ :=
  ((1 / (2 * L) : ℝ) : ℂ) * ∫ l in (-L)..L, Complex.exp (I * (dω : ℂ) * (l : ℂ))

/-- Averaged off-line exponential-minus-one remainder on `[-L, L]`. -/
private def depthDiffIntegral (L δ dω : ℝ) (u v : ℂ) : ℂ :=
  ((1 / (2 * L) : ℝ) : ℂ) * ∫ l in (-L)..L,
    Complex.exp (I * (dω : ℂ) * (l : ℂ)) *
      ((((Real.exp (δ * l) - 1 : ℝ) : ℂ) * u) - (((Real.exp ((-δ) * l) - 1 : ℝ) : ℂ) * v))

/-- Exact decomposition of `tr (twist γ F_L) z − tr (twist γ F_L) (rosatiRefl z)` into its
sinc-damped reflection mismatch and its `depthKernel`-controlled off-line remainder. -/
private theorem tr_twist_heckeAvgBump_sub_refl_eq {L : ℝ} (hL : 0 < L) (γ : ℝ) (z : ℂ) :
    tr (twist γ (heckeAvgBump L)) z - tr (twist γ (heckeAvgBump L)) (rosatiRefl z) =
      (tr (twist γ baseBump) z - tr (twist γ baseBump) (rosatiRefl z)) *
        sincFactor L (z.im - γ) +
      depthDiffIntegral L (z.re - 1 / 2) (z.im - γ)
        (tr (twist γ baseBump) z) (tr (twist γ baseBump) (rosatiRefl z)) := by
  have he1 : ∀ l : ℝ, (z - 1 / 2 - (γ : ℂ) * I) * (l : ℂ) =
      (((z.re - 1 / 2) * l : ℝ) : ℂ) + I * (((z.im - γ) * l : ℝ) : ℂ) := by
    intro l
    apply Complex.ext
    · simp
    · simp
  have he2 : ∀ l : ℝ, (rosatiRefl z - 1 / 2 - (γ : ℂ) * I) * (l : ℂ) =
      (((-(z.re - 1 / 2)) * l : ℝ) : ℂ) + I * (((z.im - γ) * l : ℝ) : ℂ) := by
    intro l
    apply Complex.ext
    · simp [rosatiRefl]; left; ring
    · simp [rosatiRefl]
  rw [tr_twist_heckeAvgBump_eq hL γ z, tr_twist_heckeAvgBump_eq hL γ (rosatiRefl z)]
  unfold sincFactor depthDiffIntegral
  have hi1 : IntervalIntegrable (fun l : ℝ =>
      Complex.exp ((z - 1 / 2 - (γ : ℂ) * I) * (l : ℂ)) * tr (twist γ baseBump) z)
      volume (-L) L :=
    ((Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).mul
      continuous_const).intervalIntegrable (μ := volume) _ _
  have hi2 : IntervalIntegrable (fun l : ℝ =>
      Complex.exp ((rosatiRefl z - 1 / 2 - (γ : ℂ) * I) * (l : ℂ)) *
        tr (twist γ baseBump) (rosatiRefl z)) volume (-L) L :=
    ((Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).mul
      continuous_const).intervalIntegrable (μ := volume) _ _
  have hiA : IntervalIntegrable (fun l : ℝ =>
      Complex.exp (I * ((z.im - γ : ℝ) : ℂ) * (l : ℂ))) volume (-L) L :=
    (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).intervalIntegrable
      (μ := volume) _ _
  have hiB : IntervalIntegrable (fun l : ℝ =>
      Complex.exp (I * ((z.im - γ : ℝ) : ℂ) * (l : ℂ)) *
        ((((Real.exp ((z.re - 1 / 2) * l) - 1 : ℝ) : ℂ) * tr (twist γ baseBump) z) -
          (((Real.exp ((-(z.re - 1 / 2)) * l) - 1 : ℝ) : ℂ) *
            tr (twist γ baseBump) (rosatiRefl z)))) volume (-L) L :=
    ((Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).mul
      (((Complex.continuous_ofReal.comp ((Real.continuous_exp.comp
        (continuous_const.mul continuous_id)).sub continuous_const)).mul continuous_const).sub
      ((Complex.continuous_ofReal.comp ((Real.continuous_exp.comp
        (continuous_const.mul continuous_id)).sub continuous_const)).mul continuous_const))).intervalIntegrable
      (μ := volume) _ _
  rw [← mul_sub ((1 / (2 * L) : ℝ) : ℂ), ← intervalIntegral.integral_sub hi1 hi2,
    mul_comm (tr (twist γ baseBump) z - tr (twist γ baseBump) (rosatiRefl z)),
    mul_assoc, ← intervalIntegral.integral_mul_const,
    ← mul_add ((1 / (2 * L) : ℝ) : ℂ), ← intervalIntegral.integral_add (hiA.mul_const _) hiB]
  congr 1
  refine intervalIntegral.integral_congr fun l _ => ?_
  rw [he1 l, he2 l, Complex.exp_add, Complex.exp_add, ← Complex.ofReal_exp, ← Complex.ofReal_exp,
    Complex.ofReal_mul (z.im - γ) l, ← mul_assoc I]
  push_cast
  ring

/-- Quadratic bound on `depthDiffIntegral` via `depthKernel L δ`. -/
private theorem normSq_depthDiffIntegral_le {L : ℝ} (hL : 0 < L) (δ dω : ℝ) (u v : ℂ) :
    Complex.normSq (depthDiffIntegral L δ dω u v) ≤
      2 * depthKernel L δ * (Complex.normSq u + Complex.normSq v) := by
  have hK2 : Real.sqrt (depthKernel L δ) ^ 2 = depthKernel L δ :=
    Real.sq_sqrt (depthKernel_nonneg L δ)
  have hB_norm : ‖depthDiffIntegral L δ dω u v‖ ≤ Real.sqrt (depthKernel L δ) * (‖u‖ + ‖v‖) := by
    unfold depthDiffIntegral
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have hI : ‖∫ l in (-L)..L,
        Complex.exp (I * (dω : ℂ) * (l : ℂ)) *
          ((((Real.exp (δ * l) - 1 : ℝ) : ℂ) * u) - (((Real.exp ((-δ) * l) - 1 : ℝ) : ℂ) * v))‖ ≤
        Real.sqrt (depthKernel L δ) * (‖u‖ + ‖v‖) * |L - -L| :=
      intervalIntegral.norm_integral_le_of_norm_le_const fun l hl => by
        rw [uIoc_of_le (by linarith)] at hl
        have hlabs : |l| ≤ L := abs_le.mpr ⟨hl.1.le, hl.2⟩
        rw [norm_mul, show I * (dω : ℂ) * (l : ℂ) = ((dω * l : ℝ) : ℂ) * I by push_cast; ring,
          Complex.norm_exp_ofReal_mul_I, one_mul]
        refine (norm_sub_le _ _).trans ?_
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs]
        have hd1 : |Real.exp (δ * l) - 1| ≤ Real.sqrt (depthKernel L δ) := by
          rw [← Real.sqrt_sq_eq_abs]
          exact Real.sqrt_le_sqrt (sq_exp_mul_sub_one_le_depthKernel hL hlabs)
        have hd2 : |Real.exp ((-δ) * l) - 1| ≤ Real.sqrt (depthKernel L δ) := by
          rw [← Real.sqrt_sq_eq_abs]
          have hdk_neg : depthKernel L (-δ) = depthKernel L δ := by
            unfold depthKernel; rw [show 2 * -δ * L = -(2 * δ * L) by ring, Real.cosh_neg]
          exact (Real.sqrt_le_sqrt (sq_exp_mul_sub_one_le_depthKernel hL hlabs)).trans_eq
            (by rw [hdk_neg])
        calc |Real.exp (δ * l) - 1| * ‖u‖ + |Real.exp ((-δ) * l) - 1| * ‖v‖
            ≤ Real.sqrt (depthKernel L δ) * ‖u‖ + Real.sqrt (depthKernel L δ) * ‖v‖ := by gcongr
          _ = Real.sqrt (depthKernel L δ) * (‖u‖ + ‖v‖) := by ring
    rw [abs_of_pos (by linarith : 0 < L - -L), sub_neg_eq_add] at hI
    calc 1 / (2 * L) * ‖∫ l in (-L)..L, _‖
        ≤ 1 / (2 * L) * (Real.sqrt (depthKernel L δ) * (‖u‖ + ‖v‖) * (L + L)) :=
          mul_le_mul_of_nonneg_left hI (by positivity)
      _ = Real.sqrt (depthKernel L δ) * (‖u‖ + ‖v‖) := by field_simp; ring
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  calc ‖depthDiffIntegral L δ dω u v‖ ^ 2
      ≤ (Real.sqrt (depthKernel L δ) * (‖u‖ + ‖v‖)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hB_norm 2
    _ = Real.sqrt (depthKernel L δ) ^ 2 * (‖u‖ + ‖v‖) ^ 2 := by ring
    _ ≤ Real.sqrt (depthKernel L δ) ^ 2 * (2 * (‖u‖ ^ 2 + ‖v‖ ^ 2)) := by
        gcongr; nlinarith [sq_nonneg (‖u‖ - ‖v‖)]
    _ = 2 * depthKernel L δ * (‖u‖ ^ 2 + ‖v‖ ^ 2) := by rw [hK2]; ring

/-- Sinc-cancelled Lorentzian bound on `(tr (twist γ h₀) ρ − tr (twist γ h₀) (1 − ρ̄)) * sincFactor`. -/
private theorem normSq_refl_sinc_le {L : ℝ} (hL : 0 < L) (γ : ℝ) (ρ : zetaZeroConfig.carrier) :
    Complex.normSq ((tr (twist γ baseBump) ρ - tr (twist γ baseBump) (rosatiRefl ρ)) *
        sincFactor L ((ρ : ℂ).im - γ)) ≤
      (max 2 (4 * Real.exp (1 / 4) * envelope baseBump ^ 2) / L ^ 2) *
        (1 / (1 + (γ - (ρ : ℂ).im) ^ 2)) := by
  have hgL_rw : 1 / (1 + (γ - (ρ : ℂ).im) ^ 2) = 1 / (1 + ((ρ : ℂ).im - γ) ^ 2) := by
    congr 2; ring
  rw [hgL_rw, Complex.normSq_eq_norm_sq]
  by_cases hdω0 : (ρ : ℂ).im - γ = 0
  · have huv0 : ‖tr (twist γ baseBump) ρ - tr (twist γ baseBump) (rosatiRefl ρ)‖ = 0 :=
      le_antisymm ((norm_tr_twist_baseBump_sub_refl_le γ ρ).trans (by rw [hdω0, abs_zero]))
        (norm_nonneg _)
    rw [norm_mul, huv0, zero_mul]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    positivity
  · rcases le_or_gt |(ρ : ℂ).im - γ| 1 with hdω1 | hdω1
    · have hnormA : ‖(tr (twist γ baseBump) ρ - tr (twist γ baseBump) (rosatiRefl ρ)) *
          sincFactor L ((ρ : ℂ).im - γ)‖ ≤ 1 / L := by
        rw [norm_mul]
        have h1 := norm_tr_twist_baseBump_sub_refl_le γ ρ
        have h2 : ‖sincFactor L ((ρ : ℂ).im - γ)‖ ≤ 1 / (L * |(ρ : ℂ).im - γ|) :=
          norm_sinc_intervalIntegral_le hL hdω0
        have hdωp : 0 < |(ρ : ℂ).im - γ| := abs_pos.mpr hdω0
        calc ‖tr (twist γ baseBump) ρ - tr (twist γ baseBump) (rosatiRefl ρ)‖ *
              ‖sincFactor L ((ρ : ℂ).im - γ)‖
            ≤ |(ρ : ℂ).im - γ| * (1 / (L * |(ρ : ℂ).im - γ|)) :=
              mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
          _ = 1 / L := by field_simp
      have h1dω : 1 + ((ρ : ℂ).im - γ) ^ 2 ≤ 2 := by
        nlinarith [sq_abs ((ρ : ℂ).im - γ), abs_nonneg ((ρ : ℂ).im - γ)]
      have h2MK : (2 : ℝ) ≤ max 2 (4 * Real.exp (1 / 4) * envelope baseBump ^ 2) :=
        le_max_left _ _
      calc ‖(tr (twist γ baseBump) ρ - tr (twist γ baseBump) (rosatiRefl ρ)) *
              sincFactor L ((ρ : ℂ).im - γ)‖ ^ 2
          ≤ (1 / L) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hnormA 2
        _ = 2 / L ^ 2 * (1 / 2) := by ring
        _ ≤ max 2 (4 * Real.exp (1 / 4) * envelope baseBump ^ 2) / L ^ 2 *
              (1 / (1 + ((ρ : ℂ).im - γ) ^ 2)) := by
            refine mul_le_mul (by gcongr) ?_ (by positivity) (by positivity)
            exact one_div_le_one_div_of_le (by positivity) h1dω
    · have hstrip := zetaZeroConfig.strip ρ ρ.2
      have hstrip' : 0 ≤ (rosatiRefl (ρ : ℂ)).re ∧ (rosatiRefl (ρ : ℂ)).re ≤ 1 := by
        simp only [rosatiRefl, Complex.sub_re, Complex.one_re, Complex.conj_re]
        exact ⟨by linarith [hstrip.2], by linarith [hstrip.1]⟩
      have hb_supp : ∀ x, baseBump x ≠ 0 → |x| ≤ 1 / 4 := fun x hx => by
        by_contra h; exact hx (baseBump_eq_zero_of_abs_ge (not_le.mp h).le)
      have hu_dec := norm_tr_twist_le (contDiff_baseBump (n := 2)) (by norm_num : (0 : ℝ) ≤ 1 / 4)
        hb_supp γ hstrip
      have hv_dec := norm_tr_twist_le (contDiff_baseBump (n := 2)) (by norm_num : (0 : ℝ) ≤ 1 / 4)
        hb_supp γ hstrip'
      have him_refl : (rosatiRefl (ρ : ℂ)).im = (ρ : ℂ).im := by simp [rosatiRefl]
      rw [him_refl] at hv_dec
      have hsinc : ‖sincFactor L ((ρ : ℂ).im - γ)‖ ≤ 1 / L :=
        (norm_sinc_intervalIntegral_le hL hdω0).trans
          (one_div_le_one_div_of_le hL (le_mul_of_one_le_right hL.le hdω1.le))
      have huv_dec : ‖tr (twist γ baseBump) ρ - tr (twist γ baseBump) (rosatiRefl ρ)‖ ≤
          2 * Real.exp (1 / 8) * envelope baseBump / (1 + |(ρ : ℂ).im - γ|) ^ 2 := by
        refine (norm_sub_le _ _).trans ?_
        have h18 : (1 / 4 : ℝ) / 2 = 1 / 8 := by norm_num
        rw [h18] at hu_dec hv_dec
        exact (add_le_add hu_dec hv_dec).trans_eq (by ring)
      have henv0 : 0 ≤ envelope baseBump := envelope_nonneg baseBump
      have hnormA : ‖(tr (twist γ baseBump) ρ - tr (twist γ baseBump) (rosatiRefl ρ)) *
            sincFactor L ((ρ : ℂ).im - γ)‖ ≤
          (2 * Real.exp (1 / 8) * envelope baseBump / L) / (1 + |(ρ : ℂ).im - γ|) ^ 2 := by
        rw [norm_mul]
        calc ‖tr (twist γ baseBump) ρ - tr (twist γ baseBump) (rosatiRefl ρ)‖ *
              ‖sincFactor L ((ρ : ℂ).im - γ)‖
            ≤ (2 * Real.exp (1 / 8) * envelope baseBump / (1 + |(ρ : ℂ).im - γ|) ^ 2) * (1 / L) :=
              mul_le_mul huv_dec hsinc (norm_nonneg _)
                (div_nonneg (mul_nonneg (by positivity) henv0) (by positivity))
          _ = (2 * Real.exp (1 / 8) * envelope baseBump / L) / (1 + |(ρ : ℂ).im - γ|) ^ 2 := by ring
      have hden : 1 + ((ρ : ℂ).im - γ) ^ 2 ≤ (1 + |(ρ : ℂ).im - γ|) ^ 4 := by
        nlinarith [sq_abs ((ρ : ℂ).im - γ), abs_nonneg ((ρ : ℂ).im - γ),
          sq_nonneg |(ρ : ℂ).im - γ|]
      have h4MK : 4 * Real.exp (1 / 4) * envelope baseBump ^ 2 ≤
          max 2 (4 * Real.exp (1 / 4) * envelope baseBump ^ 2) := le_max_right _ _
      calc ‖(tr (twist γ baseBump) ρ - tr (twist γ baseBump) (rosatiRefl ρ)) *
              sincFactor L ((ρ : ℂ).im - γ)‖ ^ 2
          ≤ ((2 * Real.exp (1 / 8) * envelope baseBump / L) / (1 + |(ρ : ℂ).im - γ|) ^ 2) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) hnormA 2
        _ = (4 * Real.exp (1 / 4) * envelope baseBump ^ 2 / L ^ 2) *
              (1 / (1 + |(ρ : ℂ).im - γ|) ^ 4) := by
            rw [div_pow, div_pow, mul_pow, mul_pow, ← Real.exp_nat_mul]
            push_cast; ring_nf
        _ ≤ (max 2 (4 * Real.exp (1 / 4) * envelope baseBump ^ 2) / L ^ 2) *
              (1 / (1 + ((ρ : ℂ).im - γ) ^ 2)) := by
            refine mul_le_mul (by gcongr) ?_ (by positivity) (by positivity)
            exact one_div_le_one_div_of_le (by positivity) hden

/-- Pointwise Carrier Bound for the `offLineDefect` summand of `heckeAvgBump L`. -/
private theorem offLineDefect_heckeAvg_summand_le {L : ℝ} (hL : 0 < L) (γ : ℝ)
    (ρ : zetaZeroConfig.carrier) :
    (zetaZeroConfig.mult ρ : ℝ) / 2 *
      Complex.normSq (tr (twist γ (heckeAvgBump L)) ρ -
        tr (twist γ (heckeAvgBump L)) (rosatiRefl ρ)) ≤
    2 * (zetaWeight (baseTwistTest γ) ρ * depthKernel L (zetaDepth ρ)) +
    2 * ((zetaZeroConfig.mult ρ : ℝ) * Complex.normSq (tr (twist γ baseBump) (rosatiRefl ρ)) *
      depthKernel L (zetaDepth ρ)) +
    (max 2 (4 * Real.exp (1 / 4) * envelope baseBump ^ 2) / L ^ 2) *
      ((zetaZeroConfig.mult ρ : ℝ) * (1 / (1 + (γ - (ρ : ℂ).im) ^ 2))) := by
  rw [tr_twist_heckeAvgBump_sub_refl_eq hL γ (ρ : ℂ)]
  have hAB : ∀ a b : ℂ, Complex.normSq (a + b) ≤ 2 * Complex.normSq a + 2 * Complex.normSq b := by
    intro a b
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
    have htri := norm_add_le a b
    have hsq := pow_le_pow_left₀ (norm_nonneg _) htri 2
    nlinarith [sq_nonneg (‖a‖ - ‖b‖)]
  have hm0 : (0 : ℝ) ≤ zetaZeroConfig.mult ρ := Nat.cast_nonneg _
  have hA := mul_le_mul_of_nonneg_left (normSq_refl_sinc_le hL γ ρ) hm0
  have hB := mul_le_mul_of_nonneg_left
    (normSq_depthDiffIntegral_le hL ((ρ : ℂ).re - 1 / 2) ((ρ : ℂ).im - γ)
      (tr (twist γ baseBump) ρ) (tr (twist γ baseBump) (rosatiRefl ρ))) hm0
  have hB' : (zetaZeroConfig.mult ρ : ℝ) *
      Complex.normSq (depthDiffIntegral L ((ρ : ℂ).re - 1 / 2) ((ρ : ℂ).im - γ)
        (tr (twist γ baseBump) ρ) (tr (twist γ baseBump) (rosatiRefl ρ))) ≤
      2 * (zetaWeight (baseTwistTest γ) ρ * depthKernel L (zetaDepth ρ)) +
      2 * ((zetaZeroConfig.mult ρ : ℝ) * Complex.normSq (tr (twist γ baseBump) (rosatiRefl ρ)) *
        depthKernel L (zetaDepth ρ)) := by
    refine hB.trans_eq ?_
    simp only [zetaWeight, baseTwistTest, zetaDepth]
    ring
  have hA' : (zetaZeroConfig.mult ρ : ℝ) *
      Complex.normSq ((tr (twist γ baseBump) ρ - tr (twist γ baseBump) (rosatiRefl ρ)) *
        sincFactor L ((ρ : ℂ).im - γ)) ≤
      (max 2 (4 * Real.exp (1 / 4) * envelope baseBump ^ 2) / L ^ 2) *
        ((zetaZeroConfig.mult ρ : ℝ) * (1 / (1 + (γ - (ρ : ℂ).im) ^ 2))) :=
    hA.trans_eq (by ring)
  calc (zetaZeroConfig.mult ρ : ℝ) / 2 * Complex.normSq _
      ≤ (zetaZeroConfig.mult ρ : ℝ) / 2 *
          (2 * Complex.normSq ((tr (twist γ baseBump) ρ - tr (twist γ baseBump) (rosatiRefl ρ)) *
              sincFactor L ((ρ : ℂ).im - γ)) +
            2 * Complex.normSq (depthDiffIntegral L ((ρ : ℂ).re - 1 / 2) ((ρ : ℂ).im - γ)
              (tr (twist γ baseBump) ρ) (tr (twist γ baseBump) (rosatiRefl ρ)))) :=
        mul_le_mul_of_nonneg_left (hAB _ _) (div_nonneg hm0 zero_le_two)
    _ = (zetaZeroConfig.mult ρ : ℝ) *
          Complex.normSq ((tr (twist γ baseBump) ρ - tr (twist γ baseBump) (rosatiRefl ρ)) *
            sincFactor L ((ρ : ℂ).im - γ)) +
        (zetaZeroConfig.mult ρ : ℝ) *
          Complex.normSq (depthDiffIntegral L ((ρ : ℂ).re - 1 / 2) ((ρ : ℂ).im - γ)
            (tr (twist γ baseBump) ρ) (tr (twist γ baseBump) (rosatiRefl ρ))) := by ring
    _ ≤ _ := by linarith [hA', hB']

/-- **Sinc-cancelled off-line defect bound.** For every `L > 0` and height `γ ∈ ℝ`, the off-line
capacity defect of `twist γ (heckeAvgBump L)` is controlled by `4 * heckeDefect (baseTwistTest γ) L`
plus an `O((1 + log(|γ| + 4)) / L²)` Lorentzian tail. -/
theorem offLineDefect_heckeAvg_le_heckeDefect_add_lorentz {L : ℝ} (hL : 0 < L) (γ : ℝ) :
    offLineDefect zetaZeroConfig (twist γ (heckeAvgBump L)) ≤
      4 * heckeDefect (baseTwistTest γ) L +
        sincLorentzConst * (1 + Real.log (|γ| + 4)) / L ^ 2 := by
  have hl_sum : Summable (fun q : XiZeroCopy => 1 / (1 + (γ - (q.1 : ℂ).im) ^ 2)) :=
    RHTower.summable_lorentzMassTerm γ
  have hgL_sum : Summable fun ρ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult ρ : ℝ) * (1 / (1 + (γ - (ρ : ℂ).im) ^ 2)) :=
    ArithmeticCastelnuovoSeveri.summable_zetaCarrier_of_xiZeroCopy
      (g := fun z : ℂ => 1 / (1 + (γ - z.im) ^ 2)) (fun _ => by positivity) hl_sum
  have hgL_eq : (∑' ρ : zetaZeroConfig.carrier,
      (zetaZeroConfig.mult ρ : ℝ) * (1 / (1 + (γ - (ρ : ℂ).im) ^ 2))) =
      RHTower.lorentzMass γ :=
    (ArithmeticCastelnuovoSeveri.tsum_xiZeroCopy_eq_zetaCarrier
      (g := fun z : ℂ => 1 / (1 + (γ - z.im) ^ 2)) hl_sum).symm
  have hd_sum1 : Summable fun ρ : zetaZeroConfig.carrier =>
      zetaWeight (baseTwistTest γ) ρ * depthKernel L (zetaDepth ρ) :=
    summable_heckeDefect (baseTwistTest γ) L
  have hd_refl_eq : (fun ρ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult ρ : ℝ) * Complex.normSq (tr (twist γ baseBump) (rosatiRefl ρ)) *
        depthKernel L (zetaDepth ρ)) =
      (fun ρ : zetaZeroConfig.carrier =>
        zetaWeight (baseTwistTest γ) ρ * depthKernel L (zetaDepth ρ)) ∘
        reflEquiv zetaZeroConfig := by
    funext ρ
    simp only [Function.comp, zetaWeight, baseTwistTest, mult_reflEquiv]
    have hdepth : zetaDepth (reflEquiv zetaZeroConfig ρ) = -zetaDepth ρ := by
      change (rosatiRefl (ρ : ℂ)).re - 1 / 2 = -((ρ : ℂ).re - 1 / 2)
      simp [rosatiRefl]; ring
    have hdk : depthKernel L (-zetaDepth ρ) = depthKernel L (zetaDepth ρ) := by
      unfold depthKernel
      rw [show 2 * -zetaDepth ρ * L = -(2 * zetaDepth ρ * L) by ring, Real.cosh_neg]
    rw [hdepth, hdk]
    rfl
  have hd_sum2 : Summable fun ρ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult ρ : ℝ) * Complex.normSq (tr (twist γ baseBump) (rosatiRefl ρ)) *
        depthKernel L (zetaDepth ρ) := by
    rw [hd_refl_eq]
    exact (Equiv.summable_iff (f := fun ρ : zetaZeroConfig.carrier =>
      zetaWeight (baseTwistTest γ) ρ * depthKernel L (zetaDepth ρ))
      (reflEquiv zetaZeroConfig)).mpr hd_sum1
  have hd_tsum2 : (∑' ρ : zetaZeroConfig.carrier,
      (zetaZeroConfig.mult ρ : ℝ) * Complex.normSq (tr (twist γ baseBump) (rosatiRefl ρ)) *
        depthKernel L (zetaDepth ρ)) = heckeDefect (baseTwistTest γ) L := by
    rw [hd_refl_eq]
    exact (reflEquiv zetaZeroConfig).tsum_eq
      (fun ρ : zetaZeroConfig.carrier => zetaWeight (baseTwistTest γ) ρ * depthKernel L (zetaDepth ρ))
  have hsF := zeta_summable_collided (contDiff_twist (contDiff_heckeAvgBump L) γ)
    (hasCompactSupport_twist (hasCompactSupport_heckeAvgBump hL) γ)
  have hsF_refl : Summable fun ρ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult ρ : ℝ) *
        Complex.normSq (tr (twist γ (heckeAvgBump L)) (rosatiRefl ρ)) := by
    have heq : (fun ρ : zetaZeroConfig.carrier =>
        (zetaZeroConfig.mult ρ : ℝ) *
          Complex.normSq (tr (twist γ (heckeAvgBump L)) (rosatiRefl ρ))) =
        (fun ρ : zetaZeroConfig.carrier =>
          (zetaZeroConfig.mult ρ : ℝ) *
            Complex.normSq (tr (twist γ (heckeAvgBump L)) ρ)) ∘ reflEquiv zetaZeroConfig := by
      funext ρ; simp only [Function.comp, mult_reflEquiv]; rfl
    rw [heq]
    exact (Equiv.summable_iff (f := fun ρ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult ρ : ℝ) * Complex.normSq (tr (twist γ (heckeAvgBump L)) ρ))
      (reflEquiv zetaZeroConfig)).mpr hsF
  have hs_def : Summable fun ρ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult ρ : ℝ) / 2 *
        Complex.normSq (tr (twist γ (heckeAvgBump L)) ρ -
          tr (twist γ (heckeAvgBump L)) (rosatiRefl ρ)) := by
    refine Summable.of_nonneg_of_le (fun _ => mul_nonneg (by positivity) (Complex.normSq_nonneg _))
      (fun ρ => ?_) (hsF.add hsF_refl)
    have hm : (0 : ℝ) ≤ zetaZeroConfig.mult ρ := Nat.cast_nonneg _
    have hnsq : Complex.normSq (tr (twist γ (heckeAvgBump L)) ρ -
        tr (twist γ (heckeAvgBump L)) (rosatiRefl ρ)) ≤
        2 * (Complex.normSq (tr (twist γ (heckeAvgBump L)) ρ) +
          Complex.normSq (tr (twist γ (heckeAvgBump L)) (rosatiRefl ρ))) := by
      rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
      have htri := norm_sub_le (tr (twist γ (heckeAvgBump L)) ρ)
        (tr (twist γ (heckeAvgBump L)) (rosatiRefl ρ))
      have hsq := pow_le_pow_left₀ (norm_nonneg _) htri 2
      nlinarith [sq_nonneg (‖tr (twist γ (heckeAvgBump L)) ρ‖ -
        ‖tr (twist γ (heckeAvgBump L)) (rosatiRefl ρ)‖)]
    nlinarith
  have hsum_rhs := ((hd_sum1.mul_left 2).add (hd_sum2.mul_left 2)).add
    (hgL_sum.mul_left (max 2 (4 * Real.exp (1 / 4) * envelope baseBump ^ 2) / L ^ 2))
  have htsum := hs_def.tsum_le_tsum (offLineDefect_heckeAvg_summand_le hL γ) hsum_rhs
  rw [offLineDefect]
  refine htsum.trans ?_
  rw [(((hd_sum1.mul_left 2).add (hd_sum2.mul_left 2))).tsum_add
      (hgL_sum.mul_left (max 2 (4 * Real.exp (1 / 4) * envelope baseBump ^ 2) / L ^ 2)),
    (hd_sum1.mul_left 2).tsum_add (hd_sum2.mul_left 2),
    tsum_mul_left, tsum_mul_left, tsum_mul_left, hgL_eq, hd_tsum2]
  change 2 * heckeDefect (baseTwistTest γ) L + 2 * heckeDefect (baseTwistTest γ) L +
      max 2 (4 * Real.exp (1 / 4) * envelope baseBump ^ 2) / L ^ 2 * RHTower.lorentzMass γ ≤ _
  have hlorentz := RHTower.lorentzMass_le_log γ
  have hlog0 : 0 ≤ Real.log (|γ| + 4) := Real.log_nonneg (by linarith [abs_nonneg γ])
  have hc_le : RHTower.xiLineTwoLogDerivConstant ≤ |RHTower.xiLineTwoLogDerivConstant| :=
    le_abs_self _
  have hmass_le : RHTower.lorentzMass γ ≤
      8 * (|RHTower.xiLineTwoLogDerivConstant| + 1) * (1 + Real.log (|γ| + 4)) := by
    nlinarith [abs_nonneg RHTower.xiLineTwoLogDerivConstant]
  have htail : max 2 (4 * Real.exp (1 / 4) * envelope baseBump ^ 2) / L ^ 2 *
      RHTower.lorentzMass γ ≤
      sincLorentzConst * (1 + Real.log (|γ| + 4)) / L ^ 2 := by
    have : max 2 (4 * Real.exp (1 / 4) * envelope baseBump ^ 2) / L ^ 2 *
        RHTower.lorentzMass γ ≤
        max 2 (4 * Real.exp (1 / 4) * envelope baseBump ^ 2) / L ^ 2 *
          (8 * (|RHTower.xiLineTwoLogDerivConstant| + 1) * (1 + Real.log (|γ| + 4))) :=
      mul_le_mul_of_nonneg_left hmass_le (by positivity)
    refine this.trans_eq ?_
    unfold sincLorentzConst
    ring
  linarith

/-! ## §5. Master prime-side + Hecke-defect theorems and scale corollaries -/

/-- **Master Prime-Polynomial + Hecke-Defect Multiplicity Theorem.**
There exists an explicit constant `C_* > 0` such that for every ordinate `γ ∈ ℝ` and every
translation scale `1 ≤ L ≤ 4 log(1 + |γ|)`:
`H(γ) ≤ C_* (1 + log(2 + |γ|) / L) − Re Π_{F_L}(⌊e^{2(L + 1/4)}⌋, −γ / 2π) + 4 heckeDefect_γ(L)`. -/
theorem exists_horizontalMultiplicity_le_primePolynomial_add_heckeDefect :
    ∃ C_star : ℝ, 0 < C_star ∧ ∀ γ L : ℝ, 1 ≤ L → L ≤ 4 * Real.log (1 + |γ|) →
      (xiHorizontalMultiplicity γ : ℝ) ≤
        C_star * (1 + Real.log (2 + |γ|) / L) -
          (primePolynomial (heckeAvgBump L) ⌊Real.exp (2 * (L + 1 / 4))⌋₊
            (-γ / (2 * Real.pi))).re +
          4 * heckeDefect (baseTwistTest γ) L := by
  obtain ⟨C_mu, hCmu0, hmu⟩ := exists_mu_le
  set B_cap := heckeAvgEnvelopeCap
  have hBcap0 : 0 ≤ B_cap := (envelope_nonneg (heckeAvgBump 1)).trans (envelope_heckeAvgBump_le le_rfl)
  set C_arch := 2 * Real.exp (1 / 4) * B_cap ^ 2 + B_cap ^ 2 * (1 / 2 + Real.pi * C_mu)
  set C_star := C_arch + 3 * sincLorentzConst + 1
  have hCs_pos : 0 < C_star := by
    have := sincLorentzConst_pos
    positivity
  refine ⟨C_star, hCs_pos, fun γ L hL1 hLmax => ?_⟩
  have hLpos : 0 < L := lt_of_lt_of_le one_pos hL1
  -- Step 1: `H(γ) ≤ D(twist γ F_L) = Re W_ζ + Δ`
  have hH := horizontalMultiplicity_le_collidedForm_heckeAvg hLpos γ
  have hs := zeta_summable_collided (contDiff_twist (contDiff_heckeAvgBump L) γ)
    (hasCompactSupport_twist (hasCompactSupport_heckeAvgBump hLpos) γ)
  have hcap := re_W_eq_collided_sub_defect (Z := zetaZeroConfig) hs
  -- Step 2: Explicit formula + `re_archPart_le_decay` at `ξ = -γ / (2π)`, `a = L + 1/4`
  set ξ := -γ / (2 * Real.pi)
  have htw : twist γ (heckeAvgBump L) = heightShift ξ (heckeAvgBump L) := twist_eq_heightShift γ _
  have hEF := re_archPart_sub_re_zetaZeroConfig_W_eq_re_primePolynomial
    (contDiff_heckeAvgBump L) (tsupport_heckeAvgBump_subset hLpos) ξ
  have harch := ArithmeticPositivityTheory.re_archPart_le_decay (by positivity : 0 ≤ L + 1 / 4)
    hCmu0 hmu (contDiff_heckeAvgBump L) (tsupport_heckeAvgBump_subset hLpos) ξ
  have h2piξ : 2 * Real.pi * |ξ| = |γ| := by
    simp only [ξ, abs_div, abs_neg, abs_of_pos Real.two_pi_pos]
    field_simp
  rw [h2piξ] at harch
  -- Bound `exp(L + 1/4) / (1 + |γ|)^4 ≤ exp(1/4)` from `L ≤ 4 log(1 + |γ|)`
  have hexp_le : Real.exp (L + 1 / 4) / (1 + |γ|) ^ 4 ≤ Real.exp (1 / 4) := by
    have h1g : 0 < 1 + |γ| := by positivity
    have hLexp : Real.exp L ≤ (1 + |γ|) ^ 4 := by
      have : L ≤ Real.log ((1 + |γ|) ^ 4) := by
        rw [Real.log_pow]; push_cast; exact hLmax
      exact (Real.exp_le_exp.mpr this).trans_eq (Real.exp_log (by positivity))
    rw [Real.exp_add, mul_comm (Real.exp L), mul_div_assoc]
    exact mul_le_of_le_one_right (Real.exp_pos _).le ((div_le_one (by positivity)).mpr hLexp)
  have henv : envelope (heckeAvgBump L) ^ 2 ≤ B_cap ^ 2 :=
    pow_le_pow_left₀ (envelope_nonneg _) (envelope_heckeAvgBump_le hL1) 2
  have hL2 := integral_norm_sq_heckeAvgBump_le hLpos
  have hlog12 : Real.log (1 + |γ|) ≤ Real.log (2 + |γ|) :=
    Real.log_le_log (by positivity) (by linarith)
  have hlog2_nn : 0 ≤ Real.log (2 + |γ|) := Real.log_nonneg (by linarith [abs_nonneg γ])
  have harch' : (archPart (heckeAvgBump L) ξ).re ≤ C_arch + Real.log (2 + |γ|) / (2 * L) := by
    change _ ≤ _ at harch
    have he_eq : 4 * ((∫ u, ‖heckeAvgBump L u‖) + ∫ u, ‖deriv (deriv (heckeAvgBump L)) u‖) =
        envelope (heckeAvgBump L) := rfl
    rw [he_eq] at harch
    have ht1 : 2 * Real.exp (L + 1 / 4) * envelope (heckeAvgBump L) ^ 2 / (1 + |γ|) ^ 4 ≤
        2 * Real.exp (1 / 4) * B_cap ^ 2 := by
      calc 2 * Real.exp (L + 1 / 4) * envelope (heckeAvgBump L) ^ 2 / (1 + |γ|) ^ 4
          = 2 * (Real.exp (L + 1 / 4) / (1 + |γ|) ^ 4) * envelope (heckeAvgBump L) ^ 2 := by ring
        _ ≤ 2 * Real.exp (1 / 4) * B_cap ^ 2 := by
            refine mul_le_mul (by linarith) henv (sq_nonneg _) (by positivity)
    have ht2 : envelope (heckeAvgBump L) ^ 2 * (1 / 2 + Real.pi * C_mu) ≤
        B_cap ^ 2 * (1 / 2 + Real.pi * C_mu) :=
      mul_le_mul_of_nonneg_right henv (by positivity)
    have ht3 : (∫ t, ‖heckeAvgBump L t‖ ^ 2) * Real.log (1 + |γ|) ≤
        Real.log (2 + |γ|) / (2 * L) := by
      calc (∫ t, ‖heckeAvgBump L t‖ ^ 2) * Real.log (1 + |γ|)
          ≤ (1 / (2 * L)) * Real.log (2 + |γ|) :=
            mul_le_mul hL2 hlog12 (Real.log_nonneg (by linarith [abs_nonneg γ])) (by positivity)
        _ = Real.log (2 + |γ|) / (2 * L) := by ring
    dsimp only [C_arch]
    linarith
  -- Step 3: Sinc-cancelled off-line defect bound
  have hdef := offLineDefect_heckeAvg_le_heckeDefect_add_lorentz hLpos γ
  have hlog4 : 1 + Real.log (|γ| + 4) ≤ 3 + Real.log (2 + |γ|) := by
    have : |γ| + 4 ≤ 2 * (2 + |γ|) := by linarith [abs_nonneg γ]
    have hl : Real.log (|γ| + 4) ≤ Real.log 2 + Real.log (2 + |γ|) := by
      calc Real.log (|γ| + 4) ≤ Real.log (2 * (2 + |γ|)) := Real.log_le_log (by positivity) this
        _ = Real.log 2 + Real.log (2 + |γ|) := Real.log_mul (by norm_num) (by positivity)
    linarith [Real.log_two_lt_d9]
  have hLsq : L ≤ L ^ 2 := by nlinarith
  have hdef_tail : sincLorentzConst * (1 + Real.log (|γ| + 4)) / L ^ 2 ≤
      3 * sincLorentzConst + sincLorentzConst * (Real.log (2 + |γ|) / L) := by
    have hpos_s := sincLorentzConst_pos
    have h1 : sincLorentzConst * (1 + Real.log (|γ| + 4)) / L ^ 2 ≤
        sincLorentzConst * (3 + Real.log (2 + |γ|)) / L := by
      calc sincLorentzConst * (1 + Real.log (|γ| + 4)) / L ^ 2
          ≤ sincLorentzConst * (3 + Real.log (2 + |γ|)) / L ^ 2 := by gcongr
        _ ≤ sincLorentzConst * (3 + Real.log (2 + |γ|)) / L :=
            div_le_div_of_nonneg_left (by positivity) hLpos hLsq
    have h2 : sincLorentzConst * (3 + Real.log (2 + |γ|)) / L =
        3 * sincLorentzConst / L + sincLorentzConst * (Real.log (2 + |γ|) / L) := by ring
    have h3 : 3 * sincLorentzConst / L ≤ 3 * sincLorentzConst :=
      div_le_self (by positivity) hL1
    linarith
  -- Step 4: Assemble `H(γ) ≤ Re W_ζ + Δ = Re A_{F_L} − Re Π_{F_L} + Δ`
  rw [htw] at hH hcap hdef
  have hW_le : (zetaZeroConfig.W (heightShift ξ (heckeAvgBump L))
      (heightShift ξ (heckeAvgBump L))).re ≤
      C_arch + Real.log (2 + |γ|) / (2 * L) -
        (primePolynomial (heckeAvgBump L) ⌊Real.exp (2 * (L + 1 / 4))⌋₊ ξ).re := by
    linarith [hEF, harch']
  have hmain : C_arch + Real.log (2 + |γ|) / (2 * L) +
      (3 * sincLorentzConst + sincLorentzConst * (Real.log (2 + |γ|) / L)) ≤
      C_star * (1 + Real.log (2 + |γ|) / L) := by
    have hhalf_eq : Real.log (2 + |γ|) / (2 * L) = (1 / 2) * (Real.log (2 + |γ|) / L) := by ring
    rw [hhalf_eq]
    dsimp only [C_star]
    have h0 : 0 ≤ Real.log (2 + |γ|) / L := div_nonneg hlog2_nn hLpos.le
    have hCa0 : 0 ≤ C_arch := by positivity
    nlinarith [sincLorentzConst_pos]
  linarith [hH, hcap, hW_le, hdef, hdef_tail, hmain]

/-- **Corollary A1 (`ΔO(T) ≪ log T` from prime-polynomial + Hecke-defect control at `L = c log T`).**
For any `0 < c ≤ 4`, there exists `C > 0` such that eventually in `T` (`atTop`), for any `M ≥ 0`,
if every off-line zero ordinate `γ` in `[T, T + 1)` satisfies
`−Re Π_{F_{c log T}}(⌊e^{2(c log T + 1/4)}⌋, −γ / 2π) + 4 heckeDefect_γ(c log T) ≤ M`,
then `ΔO(T) ≤ C (1 + M) log T`. -/
theorem exists_xiCollisionIncrement_le_log_of_prime_and_heckeDefect_at_log_scale
    {c : ℝ} (hc0 : 0 < c) (hc4 : c ≤ 4) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ M : ℝ, 0 ≤ M →
      (∀ ρ ∈ xiUnitWindowZeros T, ρ.re ≠ 1 / 2 →
        -(primePolynomial (heckeAvgBump (c * Real.log T))
            ⌊Real.exp (2 * (c * Real.log T + 1 / 4))⌋₊ (-ρ.im / (2 * Real.pi))).re +
          4 * heckeDefect (baseTwistTest ρ.im) (c * Real.log T) ≤ M) →
      (xiCollisionIncrement T : ℝ) ≤ C * (1 + M) * Real.log T := by
  obtain ⟨C_star, hCs, hmaster⟩ := exists_horizontalMultiplicity_le_primePolynomial_add_heckeDefect
  obtain ⟨C_loc, hCloc, hev_loc⟩ := exists_xiUnitWindowOrder_le_log
  set K_fib : ℝ := C_star * (1 + 2 / c) + 1
  have hKpos : 0 < K_fib := by positivity
  refine ⟨2 * K_fib * C_loc, by positivity, ?_⟩
  have hlog_ev : ∀ᶠ T : ℝ in atTop, 1 ≤ c * Real.log T :=
    (Real.tendsto_log_atTop.const_mul_atTop hc0).eventually_ge_atTop 1
  filter_upwards [hev_loc, hlog_ev, eventually_ge_atTop (4 : ℝ)] with T hloc hL1 hT4 M hM0 hhyp
  set B_real : ℝ := C_star * (1 + 2 / c) + M
  set B : ℕ := ⌊B_real⌋₊
  have hfib : ∀ ρ ∈ xiUnitWindowZeros T, ρ.re ≠ 1 / 2 → xiHorizontalMultiplicity ρ.im ≤ B := by
    intro ρ hρ hne
    obtain ⟨hS, hTle⟩ := mem_xiUnitWindowZeros.mp hρ
    have hlt1 : ρ.im < T + 1 := ((Set.Finite.mem_toFinset _).mp hS).1.2.2.2
    have him0 : 0 ≤ ρ.im := by linarith
    have habs_im : |ρ.im| = ρ.im := abs_of_nonneg him0
    have hLmax : c * Real.log T ≤ 4 * Real.log (1 + |ρ.im|) := by
      have hl1 : Real.log T ≤ Real.log (1 + |ρ.im|) :=
        Real.log_le_log (by linarith) (by rw [habs_im]; linarith)
      exact (mul_le_mul_of_nonneg_right hc4 (Real.log_nonneg (by linarith))).trans
        (mul_le_mul_of_nonneg_left hl1 (by norm_num))
    have hm := hmaster ρ.im (c * Real.log T) hL1 hLmax
    have hlog2 : Real.log (2 + |ρ.im|) ≤ 2 * Real.log T := by
      have hsq : 2 + |ρ.im| ≤ T ^ 2 := by rw [habs_im]; nlinarith
      calc Real.log (2 + |ρ.im|) ≤ Real.log (T ^ 2) := Real.log_le_log (by positivity) hsq
        _ = 2 * Real.log T := by rw [Real.log_pow]; push_cast; rfl
    have hlogT_pos : 0 < Real.log T := Real.log_pos (by linarith)
    have hdiv : Real.log (2 + |ρ.im|) / (c * Real.log T) ≤ 2 / c := by
      calc Real.log (2 + |ρ.im|) / (c * Real.log T)
          ≤ (2 * Real.log T) / (c * Real.log T) := by gcongr
        _ = 2 / c := by field_simp
    have hhr : (xiHorizontalMultiplicity ρ.im : ℝ) ≤ B_real := by
      have h1 := hhyp ρ hρ hne
      dsimp only [B_real]
      nlinarith [mul_le_mul_of_nonneg_left hdiv hCs.le]
    exact Nat.le_floor hhr
  have hinc := xiCollisionIncrement_le_two_mul_max_offLineFibre_mul_offLineOrder hfib
  have hoff_le : (xiUnitWindowOffLineOrder T : ℝ) ≤ C_loc * Real.log T :=
    (Nat.cast_le.mpr (xiUnitWindowOffLineOrder_le_order T)).trans hloc
  have hB_le : (B : ℝ) ≤ K_fib * (1 + M) := by
    have h1 : (B : ℝ) ≤ B_real := Nat.floor_le (by positivity)
    have h2 : B_real ≤ K_fib * (1 + M) := by
      have hpos_term : 0 ≤ C_star * (1 + 2 / c) * M := by positivity
      dsimp only [B_real, K_fib]
      linarith
    exact h1.trans h2
  have hlogT0 : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  calc (xiCollisionIncrement T : ℝ)
      ≤ 2 * (B : ℝ) * (xiUnitWindowOffLineOrder T : ℝ) := by exact_mod_cast hinc
    _ ≤ 2 * (K_fib * (1 + M)) * (C_loc * Real.log T) := by
        refine mul_le_mul (by linarith) hoff_le (Nat.cast_nonneg _) (by positivity)
    _ = 2 * K_fib * C_loc * (1 + M) * Real.log T := by ring

/-- Pointwise bound `Λ(n) / √n ≤ 2` for every natural `n`, used to bound `primeEnvelope` cleanly at
doubly logarithmic scale without prime cancellation. -/
private theorem vonMangoldt_div_sqrt_le_two (n : ℕ) :
    ArithmeticFunction.vonMangoldt n / Real.sqrt n ≤ 2 := by
  rcases eq_or_ne n 0 with rfl | hn0
  · simp
  · have hn_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)
    have hsq_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn_pos
    rw [div_le_iff₀ hsq_pos]
    have hvm : ArithmeticFunction.vonMangoldt n ≤ Real.log n :=
      ArithmeticFunction.vonMangoldt_le_log
    have hlog : Real.log n = 2 * Real.log (Real.sqrt n) := by
      rw [Real.log_sqrt hn_pos.le]; ring
    have hsub := Real.log_le_sub_one_of_pos hsq_pos
    linarith

/-- Unconditional `ℓ¹` prime-envelope bound for `heckeAvgBump L` (`L > 0`):
`primeEnvelope (heckeAvgBump L) N ≤ 2 * N / L`. -/
theorem primeEnvelope_heckeAvgBump_le {L : ℝ} (hL : 0 < L) (N : ℕ) :
    primeEnvelope (heckeAvgBump L) N ≤ 2 * (N : ℝ) / L := by
  unfold primeEnvelope
  -- Bound `‖EF.weilTest (heckeAvgBump L) (heckeAvgBump L) x‖ ≤ 1 / (2 * L)`
  have hwt : ∀ x : ℝ, ‖EF.weilTest (heckeAvgBump L) (heckeAvgBump L) x‖ ≤ 1 / (2 * L) := by
    intro x
    rw [weilTest_apply]
    refine (norm_integral_le_integral_norm _).trans ?_
    have hint : Integrable (fun u : ℝ => ‖heckeAvgBump L u‖) :=
      ((contDiff_heckeAvgBump L).continuous.norm).integrable_of_hasCompactSupport
        (hasCompactSupport_heckeAvgBump hL).norm
    calc ∫ u : ℝ, ‖heckeAvgBump L u * conj (heckeAvgBump L (u - x))‖
        ≤ ∫ u : ℝ, ‖heckeAvgBump L u‖ * (1 / (2 * L)) := by
          refine integral_mono
            (((contDiff_heckeAvgBump L).continuous.mul
              (Complex.continuous_conj.comp ((contDiff_heckeAvgBump L).continuous.comp
                (continuous_id.sub continuous_const)))).norm.integrable_of_hasCompactSupport
              (hasCompactSupport_heckeAvgBump hL).mul_right.norm)
            (hint.mul_const _) fun u => ?_
          dsimp only
          rw [norm_mul, Complex.norm_conj]
          have h2 : ‖heckeAvgBump L (u - x)‖ ≤ 1 / (2 * L) := by
            rw [heckeAvgBump, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg (heckeAvgReal_nonneg hL _)]
            exact heckeAvgReal_le hL _
          exact mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
      _ = (∫ u : ℝ, ‖heckeAvgBump L u‖) * (1 / (2 * L)) := integral_mul_const _ _
      _ = 1 / (2 * L) := by rw [integral_norm_heckeAvgBump hL, one_mul]
  have hterm : ∀ j : ℕ × Bool, ‖primeCoeff (heckeAvgBump L) j‖ ≤ 1 / L := by
    intro j
    unfold primeCoeff
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))]
    calc (ArithmeticFunction.vonMangoldt j.1 / Real.sqrt j.1) *
          ‖EF.weilTest (heckeAvgBump L) (heckeAvgBump L) (primeFreq j)‖
        ≤ 2 * (1 / (2 * L)) :=
          mul_le_mul (vonMangoldt_div_sqrt_le_two j.1) (hwt _) (norm_nonneg _) zero_le_two
      _ = 1 / L := by field_simp
  calc ∑ j ∈ Finset.Icc 2 N ×ˢ (Finset.univ : Finset Bool), ‖primeCoeff (heckeAvgBump L) j‖
      ≤ ∑ _j ∈ Finset.Icc 2 N ×ˢ (Finset.univ : Finset Bool), (1 / L) :=
        Finset.sum_le_sum fun j _ => hterm j
    _ = ((Finset.Icc 2 N).card * 2 : ℕ) * (1 / L) := by
        rw [Finset.sum_const, Finset.card_product, Finset.card_univ, Fintype.card_bool,
          nsmul_eq_mul]
    _ ≤ (2 * (N : ℝ)) * (1 / L) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        have hcard : (Finset.Icc 2 N).card ≤ N := by rw [Nat.card_Icc]; omega
        push_cast; linarith [(show ((Finset.Icc 2 N).card : ℝ) ≤ N by exact_mod_cast hcard)]
    _ = 2 * (N : ℝ) / L := by ring

/-- **Corollary A2 (Unconditional-in-Primes Multiplicity Bound at `L = (1/4) log log |γ|`).**
Discharging `primePolynomial` unconditionally at `L = (1/4) log log |γ|` yields an explicit
constant `C > 0` such that eventually in `cocompact ℝ`:
`H(γ) ≤ C * (log |γ| / log log |γ|) + 4 * heckeDefect (baseTwistTest γ) ((1/4) log log |γ|)`.
When `heckeDefect = 0` (in particular under RH), this recovers the Littlewood–Titchmarsh bound
`H(γ) = O(log |γ| / log log |γ|)`. -/
theorem exists_horizontalMultiplicity_le_log_div_log_log_add_heckeDefect :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ γ : ℝ in cocompact ℝ,
      (xiHorizontalMultiplicity γ : ℝ) ≤
        C * (Real.log |γ| / Real.log (Real.log |γ|)) +
          4 * heckeDefect (baseTwistTest γ) ((1 / 4) * Real.log (Real.log |γ|)) := by
  obtain ⟨C_star, hCs, hmaster⟩ := exists_horizontalMultiplicity_le_primePolynomial_add_heckeDefect
  refine ⟨12 * C_star + 8 * Real.exp (1 / 2) + 1, by positivity, ?_⟩
  have habs : Tendsto (fun γ : ℝ => |γ|) (cocompact ℝ) atTop :=
    (tendsto_norm_cocompact_atTop (E := ℝ)).congr fun γ => Real.norm_eq_abs γ
  have hlog : Tendsto (fun γ : ℝ => Real.log |γ|) (cocompact ℝ) atTop :=
    Real.tendsto_log_atTop.comp habs
  have hllog : Tendsto (fun γ : ℝ => Real.log (Real.log |γ|)) (cocompact ℝ) atTop :=
    Real.tendsto_log_atTop.comp hlog
  filter_upwards [hllog.eventually_ge_atTop 4, hlog.eventually_ge_atTop 4,
    habs.eventually_ge_atTop 4] with γ hll4 hl4 hg4
  set L := (1 / 4 : ℝ) * Real.log (Real.log |γ|)
  have hL1 : 1 ≤ L := by dsimp only [L]; linarith
  have hLpos : 0 < L := lt_of_lt_of_le one_pos hL1
  -- `L ≤ (1/4) log |γ| ≤ 4 log(1 + |γ|)` since `log x ≤ x`
  have hll_le_l : Real.log (Real.log |γ|) ≤ Real.log |γ| :=
    (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have hl_le_1g : Real.log |γ| ≤ Real.log (1 + |γ|) :=
    Real.log_le_log (by linarith) (by linarith)
  have hLmax : L ≤ 4 * Real.log (1 + |γ|) := by dsimp only [L]; linarith
  have hm := hmaster γ L hL1 hLmax
  -- Bound `−Re Π_{F_L} ≤ primeEnvelope ≤ 8 exp(1/2) * √(log |γ|) / log log |γ| ≤ 8 exp(1/2) * log |γ| / log log |γ|`
  set N := ⌊Real.exp (2 * (L + 1 / 4))⌋₊
  have hp1 : -(primePolynomial (heckeAvgBump L) N (-γ / (2 * Real.pi))).re ≤
      primeEnvelope (heckeAvgBump L) N :=
    neg_le.mp (neg_primeEnvelope_le_re_primePolynomial _ _ _)
  have hp2 := primeEnvelope_heckeAvgBump_le hLpos N
  have hN_le : (N : ℝ) ≤ Real.exp (1 / 2) * Real.sqrt (Real.log |γ|) := by
    refine (Nat.floor_le (Real.exp_pos _).le).trans_eq ?_
    have : 2 * (L + 1 / 4) = 1 / 2 + (1 / 2) * Real.log (Real.log |γ|) := by dsimp only [L]; ring
    rw [this, Real.exp_add, Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by linarith : 0 < Real.log |γ|)]
    congr 2; ring
  have hsqrt_le : Real.sqrt (Real.log |γ|) ≤ Real.log |γ| := by
    have hpos : 0 ≤ Real.sqrt (Real.log |γ|) := Real.sqrt_nonneg _
    have h1 : 1 ≤ Real.sqrt (Real.log |γ|) := by
      rw [Real.le_sqrt (by norm_num) (by linarith)]
      linarith
    calc Real.sqrt (Real.log |γ|) ≤ Real.sqrt (Real.log |γ|) * Real.sqrt (Real.log |γ|) :=
          le_mul_of_one_le_right hpos h1
      _ = Real.log |γ| := Real.mul_self_sqrt (by linarith)
  have hp_bound : -(primePolynomial (heckeAvgBump L) N (-γ / (2 * Real.pi))).re ≤
      8 * Real.exp (1 / 2) * (Real.log |γ| / Real.log (Real.log |γ|)) := by
    calc -(primePolynomial (heckeAvgBump L) N (-γ / (2 * Real.pi))).re
        ≤ 2 * (N : ℝ) / L := hp1.trans hp2
      _ ≤ 2 * (Real.exp (1 / 2) * Real.log |γ|) / ((1 / 4) * Real.log (Real.log |γ|)) := by
          dsimp only [L]
          refine div_le_div_of_nonneg_right ?_ (by positivity)
          nlinarith [Real.exp_pos (1 / 2), hN_le, hsqrt_le]
      _ = 8 * Real.exp (1 / 2) * (Real.log |γ| / Real.log (Real.log |γ|)) := by field_simp; ring
  -- Bound `C_star * (1 + log(2 + |γ|) / L) ≤ 12 * C_star * (log |γ| / log log |γ|)`
  have hlog2g : Real.log (2 + |γ|) ≤ 2 * Real.log |γ| := by
    have : 2 + |γ| ≤ |γ| ^ 2 := by nlinarith
    calc Real.log (2 + |γ|) ≤ Real.log (|γ| ^ 2) := Real.log_le_log (by positivity) this
      _ = 2 * Real.log |γ| := by rw [Real.log_pow]; push_cast; rfl
  have h1_le_ratio : 1 ≤ Real.log |γ| / Real.log (Real.log |γ|) :=
    (one_le_div (by linarith)).mpr hll_le_l
  have harch_bound : C_star * (1 + Real.log (2 + |γ|) / L) ≤
      12 * C_star * (Real.log |γ| / Real.log (Real.log |γ|)) := by
    have hdiv : Real.log (2 + |γ|) / L ≤ 8 * (Real.log |γ| / Real.log (Real.log |γ|)) := by
      dsimp only [L]
      calc Real.log (2 + |γ|) / ((1 / 4) * Real.log (Real.log |γ|))
          ≤ (2 * Real.log |γ|) / ((1 / 4) * Real.log (Real.log |γ|)) := by gcongr
        _ = 8 * (Real.log |γ| / Real.log (Real.log |γ|)) := by field_simp; ring
    nlinarith [hCs]
  have hratio_nn : 0 ≤ Real.log |γ| / Real.log (Real.log |γ|) := div_nonneg (by linarith) (by linarith)
  linarith [hm, hp_bound, harch_bound]

end GaloisForLFunctions.ConjugateDiagonalGeometry

end

#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.xiCollisionIncrement_le_two_mul_max_offLineFibre_mul_offLineOrder
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.horizontalMultiplicity_le_collidedForm_heckeAvg
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.offLineDefect_heckeAvg_le_heckeDefect_add_lorentz
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.exists_horizontalMultiplicity_le_primePolynomial_add_heckeDefect
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.exists_xiCollisionIncrement_le_log_of_prime_and_heckeDefect_at_log_scale
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.exists_horizontalMultiplicity_le_log_div_log_log_add_heckeDefect
