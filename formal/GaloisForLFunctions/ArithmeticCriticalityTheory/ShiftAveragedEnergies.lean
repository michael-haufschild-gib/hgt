import GaloisForLFunctions.ArithmeticCriticalityTheory.ShiftAveragedShifts

/-!
# Averaging the two-sided energies over the shift

The reflected difference energy `D_a(u)`, the same-side energy `S_a(u)` and the source
`4 sinh(a/2) ∫ u² m_a sinh(x/2)` of the shifted ground states are integrable in `a > 0`, and

    ∫_0^∞ D_a(u) da = ∫ dm(t) ∫_0^t K(x, t−x) (u(x) − u(t−x))² dx,
    ∫_0^∞ S_a(u) da = ∫ dm(t) ∫_{x>0} K(x, x+t) (u(x) − u(x+t))² dx,
    ∫_0^∞ 4 sinh(a/2) ∫_{x>0} u² m_a sinh(x/2) dx da = 2 ∫_{x>0} u(x)² sinh²(x/2) dx,

with `K(x,y) = G(x−y) − G(x+y)` and `dm = archLevyDensity dt + Σ Λ(n) n^{−1/2} δ_{log n}`. The
exchanges of the `a`-integral with `dm` use the nonnegativity of all integrands, the bound
`O(t)` of the averaged shifts near `t = 0`, and their superexponential decay `Φ((t − 2R)/2)`
at the prime points `t = log n`.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar

noncomputable section

namespace GaloisForLFunctions.ArithmeticCriticalityTheory

/-! ### Integrability of a nonnegative series with summable integrals -/

theorem integrable_tsum_of_nonneg {μ : Measure ℝ} {F : ℕ → ℝ → ℝ}
    (hF_int : ∀ n, Integrable (F n) μ) (hF_nonneg : ∀ n, ∀ᵐ a ∂μ, 0 ≤ F n a)
    (hF_sum : Summable fun n => ∫ a, F n a ∂μ) :
    Integrable (fun a => ∑' n, F n a) μ := by
  have hall : ∀ᵐ a ∂μ, ∀ n, 0 ≤ F n a := ae_all_iff.mpr hF_nonneg
  have hlin : ∫⁻ a, ∑' n, ENNReal.ofReal (F n a) ∂μ = ENNReal.ofReal (∑' n, ∫ a, F n a ∂μ) := by
    rw [lintegral_tsum (fun n => (hF_int n).aemeasurable.ennreal_ofReal),
      ENNReal.ofReal_tsum_of_nonneg (fun n => integral_nonneg_of_ae (hF_nonneg n)) hF_sum]
    congr 1
    funext n
    exact (ofReal_integral_eq_lintegral_ofReal (hF_int n) (hF_nonneg n)).symm
  have hne : ∫⁻ a, ∑' n, ENNReal.ofReal (F n a) ∂μ ≠ ⊤ := by
    rw [hlin]
    exact ENNReal.ofReal_ne_top
  have hmeasE : AEMeasurable (fun a => ∑' n, ENNReal.ofReal (F n a)) μ :=
    AEMeasurable.tsum fun n => (hF_int n).aemeasurable.ennreal_ofReal
  have hae : ∀ᵐ a ∂μ, Summable fun n => F n a := by
    filter_upwards [ae_lt_top' hmeasE hne, hall] with a ha hnn
    exact (ENNReal.summable_toReal ha.ne).congr fun n => ENNReal.toReal_ofReal (hnn n)
  have hmeasR : AEStronglyMeasurable (fun a => ∑' n, F n a) μ := by
    have h : (fun a => (∑' n, ENNReal.ofReal (F n a)).toReal) =ᵐ[μ] fun a => ∑' n, F n a := by
      filter_upwards [hall] with a hnn
      rw [ENNReal.tsum_toReal_eq (fun n => ENNReal.ofReal_ne_top)]
      exact tsum_congr fun n => ENNReal.toReal_ofReal (hnn n)
    exact hmeasE.ennreal_toReal.aestronglyMeasurable.congr h
  refine ⟨hmeasR, ?_⟩
  have hnn' : 0 ≤ᵐ[μ] fun a => ∑' n, F n a := by
    filter_upwards [hall] with a hnn
    exact tsum_nonneg hnn
  rw [hasFiniteIntegral_iff_ofReal hnn']
  calc ∫⁻ a, ENNReal.ofReal (∑' n, F n a) ∂μ
      = ∫⁻ a, ∑' n, ENNReal.ofReal (F n a) ∂μ := by
        refine lintegral_congr_ae ?_
        filter_upwards [hae, hall] with a ha hnn
        exact ENNReal.ofReal_tsum_of_nonneg hnn ha
    _ < ⊤ := lt_top_iff_ne_top.mpr hne

/-! ### Superexponential decay at the prime points -/

theorem exists_riemannKernelReal_le_exp_eight :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, riemannKernelReal x ≤ C * Real.exp (-(8 * |x|)) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_riemannPhiKernel_le_exp (B := 8) (by norm_num)
  refine ⟨C, hC0, fun x => ?_⟩
  have h := hC x
  rwa [riemannPhiKernel_eq_ofReal, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (riemannKernelReal_pos x)] at h

theorem vonMangoldtAtom_le_log (n : ℕ) : vonMangoldtAtom n ≤ Real.log n := by
  unfold vonMangoldtAtom
  split_ifs with hn
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    calc (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n
        ≤ ArithmeticFunction.vonMangoldt n / 1 :=
          div_le_div_of_nonneg_left ArithmeticFunction.vonMangoldt_nonneg one_pos
            (Real.one_le_sqrt.mpr hn1)
      _ = ArithmeticFunction.vonMangoldt n := div_one _
      _ ≤ Real.log n := ArithmeticFunction.vonMangoldt_le_log
  · exact Real.log_natCast_nonneg n

/-- `Σ Λ(n) n^{−1/2} (1 + log n) Φ((log n − c)/2) < ∞`. -/
theorem summable_atom_mul_one_add_log_mul_kernel_half (c : ℝ) :
    Summable fun n : ℕ =>
      vonMangoldtAtom n * (1 + Real.log n) * riemannKernelReal ((Real.log n - c) / 2) := by
  obtain ⟨C, hC0, hC⟩ := exists_riemannKernelReal_le_exp_eight
  have hmaj : Summable fun n : ℕ => (2 * C * Real.exp (4 * c)) * (1 / (n : ℝ) ^ 2) :=
    (Real.summable_one_div_nat_pow.mpr (by norm_num)).mul_left _
  refine Summable.of_norm_bounded_eventually hmaj ?_
  rw [Nat.cofinite_eq_atTop, Filter.eventually_atTop]
  refine ⟨2, fun n hn => ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hlog0 : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hlogn : Real.log n ≤ n := (Real.log_le_sub_one_of_pos hn0).trans (by linarith)
  have hΛ := vonMangoldtAtom_le_log n
  have hΛ0 := vonMangoldtAtom_nonneg n
  have hK := (riemannKernelReal_pos ((Real.log n - c) / 2)).le
  have hΦ : riemannKernelReal ((Real.log n - c) / 2) ≤
      C * Real.exp (4 * c) * (1 / (n : ℝ) ^ 4) := by
    refine (hC _).trans ?_
    have h1 : Real.exp (-(8 * |(Real.log n - c) / 2|)) ≤
        Real.exp (-(8 * ((Real.log n - c) / 2))) :=
      Real.exp_le_exp.mpr (by linarith [le_abs_self ((Real.log n - c) / 2)])
    have h2 : Real.exp (-(8 * ((Real.log n - c) / 2))) =
        Real.exp (4 * c) * (1 / (n : ℝ) ^ 4) := by
      rw [show -(8 * ((Real.log n - c) / 2)) = 4 * c + -(4 * Real.log n) by ring, Real.exp_add]
      congr 1
      rw [Real.exp_neg, show (4 : ℝ) * Real.log n = ((4 : ℕ) : ℝ) * Real.log n by norm_num,
        Real.exp_nat_mul, Real.exp_log hn0, one_div]
    calc C * Real.exp (-(8 * |(Real.log n - c) / 2|))
        ≤ C * Real.exp (-(8 * ((Real.log n - c) / 2))) := mul_le_mul_of_nonneg_left h1 hC0
      _ = C * Real.exp (4 * c) * (1 / (n : ℝ) ^ 4) := by rw [h2]; ring
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg hΛ0 (by linarith)) hK)]
  have hCe : 0 ≤ C * Real.exp (4 * c) * (1 / (n : ℝ) ^ 4) := by positivity
  calc vonMangoldtAtom n * (1 + Real.log n) * riemannKernelReal ((Real.log n - c) / 2)
      ≤ (n : ℝ) * (2 * n) * (C * Real.exp (4 * c) * (1 / (n : ℝ) ^ 4)) := by
        exact mul_le_mul (mul_le_mul (hΛ.trans hlogn) (by linarith) (by linarith) hn0.le) hΦ hK
          (by positivity)
    _ = (2 * C * Real.exp (4 * c)) * (1 / (n : ℝ) ^ 2) := by
        field_simp

theorem summable_atom_mul_log_mul_kernel_half (c : ℝ) :
    Summable fun n : ℕ =>
      vonMangoldtAtom n * Real.log n * riemannKernelReal ((Real.log n - c) / 2) :=
  (summable_atom_mul_one_add_log_mul_kernel_half c).of_nonneg_of_le
    (fun n => mul_nonneg (mul_nonneg (vonMangoldtAtom_nonneg n) (Real.log_natCast_nonneg n))
      (riemannKernelReal_pos _).le)
    (fun n => mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by linarith) (vonMangoldtAtom_nonneg n))
      (riemannKernelReal_pos _).le)

theorem summable_atom_mul_kernel_half :
    Summable fun n : ℕ => vonMangoldtAtom n * riemannKernelReal (Real.log n / 2) := by
  refine (summable_atom_mul_one_add_log_mul_kernel_half 0).of_nonneg_of_le
    (fun n => mul_nonneg (vonMangoldtAtom_nonneg n) (riemannKernelReal_pos _).le) (fun n => ?_)
  rw [sub_zero]
  have := Real.log_natCast_nonneg n
  calc vonMangoldtAtom n * riemannKernelReal (Real.log n / 2)
      = vonMangoldtAtom n * 1 * riemannKernelReal (Real.log n / 2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by linarith) (vonMangoldtAtom_nonneg n))
        (riemannKernelReal_pos _).le

/-! ### Pointwise nonnegativity of the per-shift integrals -/

theorem integral_reflectedDifference_shiftedGroundState_nonneg {a : ℝ} (ha : 0 < a) (u : ℝ → ℝ)
    (t : ℝ) :
    0 ≤ ∫ x in Ioo (0 : ℝ) t, reflectedDifferenceJump (shiftedGroundState a) u t x := by
  refine setIntegral_nonneg measurableSet_Ioo fun x hx => ?_
  rw [reflectedDifferenceJump_shiftedGroundState]
  exact mul_nonneg (mul_nonneg (shiftDifference_nonneg_of_nonneg ha.le hx.1.le)
    (shiftDifference_nonneg_of_nonneg ha.le (by linarith [hx.2]))) (sq_nonneg _)

theorem integral_sameSide_shiftedGroundState_nonneg {a : ℝ} (ha : 0 < a) (u : ℝ → ℝ) {t : ℝ}
    (ht : 0 ≤ t) :
    0 ≤ ∫ x in Ioi (0 : ℝ), sameSideGroundJump (shiftedGroundState a) u t x := by
  refine setIntegral_nonneg measurableSet_Ioi fun x hx => ?_
  rw [sameSideGroundJump_shiftedGroundState]
  have hx0 : 0 < x := hx
  exact mul_nonneg (mul_nonneg (shiftDifference_nonneg_of_nonneg ha.le hx0.le)
    (shiftDifference_nonneg_of_nonneg ha.le (by linarith))) (sq_nonneg _)

/-! ### The archimedean part of the reflected energy -/

theorem measurable_reflectedShift_prod {u : ℝ → ℝ} (hu : Continuous u) :
    Measurable fun p : ℝ × ℝ => ∫ x in Ioo (0 : ℝ) p.2,
      shiftDifference p.1 x * shiftDifference p.1 (p.2 - x) * (u x - u (p.2 - x)) ^ 2 := by
  have hF : Measurable fun q : (ℝ × ℝ) × ℝ =>
      if 0 < q.2 ∧ q.2 < q.1.2 then
        shiftDifference q.1.1 q.2 * shiftDifference q.1.1 (q.1.2 - q.2) *
          (u q.2 - u (q.1.2 - q.2)) ^ 2
      else 0 := by
    have hfst : Continuous fun q : (ℝ × ℝ) × ℝ => q.1.1 := continuous_fst.fst
    have hmid : Continuous fun q : (ℝ × ℝ) × ℝ => q.1.2 := continuous_fst.snd
    have hc : Continuous fun q : (ℝ × ℝ) × ℝ =>
        shiftDifference q.1.1 q.2 * shiftDifference q.1.1 (q.1.2 - q.2) *
          (u q.2 - u (q.1.2 - q.2)) ^ 2 :=
      ((continuous_shiftDifference_uncurry.comp (hfst.prodMk continuous_snd)).mul
        (continuous_shiftDifference_uncurry.comp (hfst.prodMk (hmid.sub continuous_snd)))).mul
        (((hu.comp continuous_snd).sub (hu.comp (hmid.sub continuous_snd))).pow 2)
    refine Measurable.ite ?_ hc.measurable measurable_const
    rw [Set.setOf_and]
    exact (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd hmid.measurable)
  have h := (hF.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable
  have heq : (fun p : ℝ × ℝ => ∫ x in Ioo (0 : ℝ) p.2,
      shiftDifference p.1 x * shiftDifference p.1 (p.2 - x) * (u x - u (p.2 - x)) ^ 2) =
      fun p => ∫ x, (if 0 < x ∧ x < p.2 then
        shiftDifference p.1 x * shiftDifference p.1 (p.2 - x) * (u x - u (p.2 - x)) ^ 2
        else 0) := by
    funext p
    rw [← integral_indicator measurableSet_Ioo]
    congr 1
    funext x
    simp only [Set.indicator_apply, mem_Ioo]
  rw [heq]
  exact h

theorem integrable_archLevy_reflected_prod {u : ℝ → ℝ} {M : ℝ} (hu : Continuous u)
    (hM : ∀ x, |u x| ≤ M) :
    Integrable (Function.uncurry fun a t => archLevyDensity t *
        ∫ x in Ioo (0 : ℝ) t, reflectedDifferenceJump (shiftedGroundState a) u t x)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hmeas : AEStronglyMeasurable (Function.uncurry fun a t => archLevyDensity t *
      ∫ x in Ioo (0 : ℝ) t, reflectedDifferenceJump (shiftedGroundState a) u t x)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    have e : (Function.uncurry fun a t => archLevyDensity t *
        ∫ x in Ioo (0 : ℝ) t, reflectedDifferenceJump (shiftedGroundState a) u t x) =
        fun p : ℝ × ℝ => archLevyDensity p.2 * ∫ x in Ioo (0 : ℝ) p.2,
          shiftDifference p.1 x * shiftDifference p.1 (p.2 - x) * (u x - u (p.2 - x)) ^ 2 := by
      funext p
      show archLevyDensity p.2 *
        (∫ x in Ioo (0 : ℝ) p.2, reflectedDifferenceJump (shiftedGroundState p.1) u p.2 x) = _
      congr 1
      exact setIntegral_congr_fun measurableSet_Ioo fun x _ =>
        reflectedDifferenceJump_shiftedGroundState p.1 u p.2 x
    rw [e]
    exact ((measurable_archLevyDensity.comp measurable_snd).mul
      (measurable_reflectedShift_prod hu)).aestronglyMeasurable
  rw [integrable_prod_iff' hmeas]
  refine ⟨ae_restrict_of_forall_mem measurableSet_Ioi fun t _ => ?_, ?_⟩
  · show Integrable (fun a => archLevyDensity t *
      ∫ x in Ioo (0 : ℝ) t, reflectedDifferenceJump (shiftedGroundState a) u t x)
      (volume.restrict (Ioi 0))
    exact (integrableOn_reflectedDifferenceIntegral_shiftedGroundState hu t).const_mul _
  · have hdom : Integrable (fun t => (4 * M ^ 2 * riemannKernelReal 0) * (archLevyDensity t * t))
        (volume.restrict (Ioi 0)) := integrableOn_archLevyDensity_mul_id.const_mul _
    have hint : Integrable (fun t => archLevyDensity t * averagedReflectedShift u t)
        (volume.restrict (Ioi 0)) := by
      refine hdom.mono' (measurable_archLevyDensity.mul
        (measurable_averagedReflectedShift hu)).aestronglyMeasurable
        (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_)
      have ht0 : 0 < t := ht
      have hL := archLevyDensity_pos ht0
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hL.le (averagedReflectedShift_nonneg u t))]
      calc archLevyDensity t * averagedReflectedShift u t
          ≤ archLevyDensity t * (4 * M ^ 2 * riemannKernelReal 0 * t) :=
            mul_le_mul_of_nonneg_left (averagedReflectedShift_le_linear hM ht0) hL.le
        _ = _ := by ring
    refine hint.congr (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_)
    have ht0 : 0 < t := ht
    have hL := archLevyDensity_pos ht0
    show archLevyDensity t * averagedReflectedShift u t = ∫ a in Ioi (0 : ℝ),
      ‖archLevyDensity t * ∫ x in Ioo (0 : ℝ) t, reflectedDifferenceJump (shiftedGroundState a) u t x‖
    rw [← integral_Ioi_reflectedDifferenceIntegral_shiftedGroundState hu t, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun a ha => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hL.le
      (integral_reflectedDifference_shiftedGroundState_nonneg ha u t))]

theorem integral_Ioi_archReflected_shiftedGroundState {u : ℝ → ℝ} {M : ℝ} (hu : Continuous u)
    (hM : ∀ x, |u x| ≤ M) :
    (∫ a in Ioi (0 : ℝ), ∫ t in Ioi (0 : ℝ), archLevyDensity t *
        ∫ x in Ioo (0 : ℝ) t, reflectedDifferenceJump (shiftedGroundState a) u t x) =
      ∫ t in Ioi (0 : ℝ), archLevyDensity t * averagedReflectedShift u t := by
  rw [integral_integral_swap (integrable_archLevy_reflected_prod hu hM)]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  rw [← integral_Ioi_reflectedDifferenceIntegral_shiftedGroundState hu t, ← integral_const_mul]

theorem integrableOn_archReflected_shiftedGroundState {u : ℝ → ℝ} {M : ℝ} (hu : Continuous u)
    (hM : ∀ x, |u x| ≤ M) :
    IntegrableOn (fun a => ∫ t in Ioi (0 : ℝ), archLevyDensity t *
      ∫ x in Ioo (0 : ℝ) t, reflectedDifferenceJump (shiftedGroundState a) u t x) (Ioi 0) :=
  (integrable_archLevy_reflected_prod hu hM).integral_prod_left

/-! ### The prime part of the reflected energy -/

theorem summable_atom_mul_averagedReflectedShift {u : ℝ → ℝ} {M R : ℝ} (hM : ∀ x, |u x| ≤ M)
    (hsupp : ∀ x, R < |x| → u x = 0) :
    Summable fun n : ℕ => vonMangoldtAtom n * averagedReflectedShift u (Real.log n) := by
  have hmaj := (summable_atom_mul_log_mul_kernel_half (2 * R)).mul_left (4 * M ^ 2)
  refine Summable.of_norm_bounded_eventually hmaj ?_
  rw [Nat.cofinite_eq_atTop, Filter.eventually_atTop]
  obtain ⟨N, hN⟩ := exists_nat_ge (Real.exp (2 * R))
  refine ⟨max N 2, fun n hn => ?_⟩
  have hn2 : 2 ≤ n := le_trans (le_max_right _ _) hn
  have hnN : (N : ℝ) ≤ n := by exact_mod_cast le_trans (le_max_left _ _) hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlog : 2 * R ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le hn0]
    exact hN.trans hnN
  have hlog0 : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hΛ := vonMangoldtAtom_nonneg n
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hΛ (averagedReflectedShift_nonneg u _))]
  calc vonMangoldtAtom n * averagedReflectedShift u (Real.log n)
      ≤ vonMangoldtAtom n *
        (4 * M ^ 2 * riemannKernelReal ((Real.log n - 2 * R) / 2) * Real.log n) :=
        mul_le_mul_of_nonneg_left (averagedReflectedShift_le_decay hM hsupp hlog hlog0) hΛ
    _ = 4 * M ^ 2 * (vonMangoldtAtom n * Real.log n *
        riemannKernelReal ((Real.log n - 2 * R) / 2)) := by ring

theorem integrable_atom_reflected_term {u : ℝ → ℝ} (hu : Continuous u) (n : ℕ) :
    Integrable (fun a => vonMangoldtAtom n * ∫ x in Ioo (0 : ℝ) (Real.log n),
      reflectedDifferenceJump (shiftedGroundState a) u (Real.log n) x) (volume.restrict (Ioi 0)) :=
  (integrableOn_reflectedDifferenceIntegral_shiftedGroundState hu _).const_mul _

theorem integral_Ioi_atom_reflected_term {u : ℝ → ℝ} (hu : Continuous u) (n : ℕ) :
    (∫ a in Ioi (0 : ℝ), vonMangoldtAtom n * ∫ x in Ioo (0 : ℝ) (Real.log n),
      reflectedDifferenceJump (shiftedGroundState a) u (Real.log n) x) =
      vonMangoldtAtom n * averagedReflectedShift u (Real.log n) := by
  rw [integral_const_mul, integral_Ioi_reflectedDifferenceIntegral_shiftedGroundState hu]

theorem integral_Ioi_norm_atom_reflected_term {u : ℝ → ℝ} (hu : Continuous u) (n : ℕ) :
    (∫ a in Ioi (0 : ℝ), ‖vonMangoldtAtom n * ∫ x in Ioo (0 : ℝ) (Real.log n),
      reflectedDifferenceJump (shiftedGroundState a) u (Real.log n) x‖) =
      vonMangoldtAtom n * averagedReflectedShift u (Real.log n) := by
  rw [← integral_Ioi_atom_reflected_term hu n]
  refine setIntegral_congr_fun measurableSet_Ioi fun a ha => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (vonMangoldtAtom_nonneg n)
    (integral_reflectedDifference_shiftedGroundState_nonneg ha u _))]

theorem integral_Ioi_primeReflected_shiftedGroundState {u : ℝ → ℝ} {M R : ℝ} (hu : Continuous u)
    (hM : ∀ x, |u x| ≤ M) (hsupp : ∀ x, R < |x| → u x = 0) :
    (∫ a in Ioi (0 : ℝ), ∑' n : ℕ, vonMangoldtAtom n * ∫ x in Ioo (0 : ℝ) (Real.log n),
        reflectedDifferenceJump (shiftedGroundState a) u (Real.log n) x) =
      ∑' n : ℕ, vonMangoldtAtom n * averagedReflectedShift u (Real.log n) := by
  have hF_sum : Summable fun n : ℕ => ∫ a in Ioi (0 : ℝ), ‖vonMangoldtAtom n *
      ∫ x in Ioo (0 : ℝ) (Real.log n),
        reflectedDifferenceJump (shiftedGroundState a) u (Real.log n) x‖ :=
    (summable_atom_mul_averagedReflectedShift hM hsupp).congr fun n =>
      (integral_Ioi_norm_atom_reflected_term hu n).symm
  rw [← integral_tsum_of_summable_integral_norm (integrable_atom_reflected_term hu) hF_sum]
  exact tsum_congr fun n => integral_Ioi_atom_reflected_term hu n

theorem integrableOn_primeReflected_shiftedGroundState {u : ℝ → ℝ} {M R : ℝ}
    (hu : Continuous u) (hM : ∀ x, |u x| ≤ M) (hsupp : ∀ x, R < |x| → u x = 0) :
    IntegrableOn (fun a => ∑' n : ℕ, vonMangoldtAtom n * ∫ x in Ioo (0 : ℝ) (Real.log n),
      reflectedDifferenceJump (shiftedGroundState a) u (Real.log n) x) (Ioi 0) := by
  refine integrable_tsum_of_nonneg (integrable_atom_reflected_term hu) (fun n => ?_) ?_
  · exact ae_restrict_of_forall_mem measurableSet_Ioi fun a ha =>
      mul_nonneg (vonMangoldtAtom_nonneg n)
        (integral_reflectedDifference_shiftedGroundState_nonneg ha u _)
  · exact (summable_atom_mul_averagedReflectedShift hM hsupp).congr fun n =>
      (integral_Ioi_atom_reflected_term hu n).symm

/-! ### The averaged reflected energy -/

/-- The averaged reflected energy `∫ dm(t) ∫_0^t K(x, t−x) (u(x) − u(t−x))² dx`. -/
def averagedReflectedEnergy (u : ℝ → ℝ) : ℝ :=
  (∫ t in Ioi (0 : ℝ), archLevyDensity t * averagedReflectedShift u t) +
    ∑' n : ℕ, vonMangoldtAtom n * averagedReflectedShift u (Real.log n)

theorem integrableOn_reflectedDifferenceEnergy_shiftedGroundState {u : ℝ → ℝ}
    (hu : Continuous u) (huc : HasCompactSupport u) :
    IntegrableOn (fun a => reflectedDifferenceEnergy (shiftedGroundState a) u) (Ioi 0) := by
  obtain ⟨R, _, hsupp⟩ := exists_support_radius huc
  obtain ⟨M, hM'⟩ := hu.bounded_above_of_compact_support huc
  have hM : ∀ x, |u x| ≤ M := fun x => by
    rw [← Real.norm_eq_abs]
    exact hM' x
  refine ((integrableOn_archReflected_shiftedGroundState hu hM).add
    (integrableOn_primeReflected_shiftedGroundState hu hM hsupp)).congr
    (Eventually.of_forall fun a => ?_)
  rfl

/-- **The shift average of the reflected difference energy.** -/
theorem integral_Ioi_reflectedDifferenceEnergy_shiftedGroundState {u : ℝ → ℝ}
    (hu : Continuous u) (huc : HasCompactSupport u) :
    (∫ a in Ioi (0 : ℝ), reflectedDifferenceEnergy (shiftedGroundState a) u) =
      averagedReflectedEnergy u := by
  obtain ⟨R, _, hsupp⟩ := exists_support_radius huc
  obtain ⟨M, hM'⟩ := hu.bounded_above_of_compact_support huc
  have hM : ∀ x, |u x| ≤ M := fun x => by
    rw [← Real.norm_eq_abs]
    exact hM' x
  unfold reflectedDifferenceEnergy averagedReflectedEnergy
  rw [integral_add (integrableOn_archReflected_shiftedGroundState hu hM)
    (integrableOn_primeReflected_shiftedGroundState hu hM hsupp),
    integral_Ioi_archReflected_shiftedGroundState hu hM,
    integral_Ioi_primeReflected_shiftedGroundState hu hM hsupp]

/-! ### The archimedean part of the same-side energy -/

theorem measurable_sameSideShift_prod {u : ℝ → ℝ} (hu : Continuous u) :
    Measurable fun p : ℝ × ℝ => ∫ x in Ioi (0 : ℝ),
      shiftDifference p.1 x * shiftDifference p.1 (x + p.2) * (u x - u (x + p.2)) ^ 2 := by
  have hfst : Continuous fun q : (ℝ × ℝ) × ℝ => q.1.1 := continuous_fst.fst
  have hmid : Continuous fun q : (ℝ × ℝ) × ℝ => q.1.2 := continuous_fst.snd
  have hc : Continuous fun q : (ℝ × ℝ) × ℝ =>
      shiftDifference q.1.1 q.2 * shiftDifference q.1.1 (q.2 + q.1.2) *
        (u q.2 - u (q.2 + q.1.2)) ^ 2 :=
    ((continuous_shiftDifference_uncurry.comp (hfst.prodMk continuous_snd)).mul
      (continuous_shiftDifference_uncurry.comp (hfst.prodMk (continuous_snd.add hmid)))).mul
      (((hu.comp continuous_snd).sub (hu.comp (continuous_snd.add hmid))).pow 2)
  exact (hc.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioi 0))).measurable

theorem integrable_archLevy_sameSide_prod {u : ℝ → ℝ} {M R L : ℝ} (hu : Continuous u)
    (huc : HasCompactSupport u) (hR : 0 ≤ R) (hM : ∀ x, |u x| ≤ M)
    (hsupp : ∀ x, R < |x| → u x = 0)
    (hL : ∀ x ∈ Icc (-R - 1) (R + 1), ∀ y ∈ Icc (-R - 1) (R + 1), |u y - u x| ≤ L * |y - x|) :
    Integrable (Function.uncurry fun a t => archLevyDensity t *
        ∫ x in Ioi (0 : ℝ), sameSideGroundJump (shiftedGroundState a) u t x)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hmeas : AEStronglyMeasurable (Function.uncurry fun a t => archLevyDensity t *
      ∫ x in Ioi (0 : ℝ), sameSideGroundJump (shiftedGroundState a) u t x)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    have e : (Function.uncurry fun a t => archLevyDensity t *
        ∫ x in Ioi (0 : ℝ), sameSideGroundJump (shiftedGroundState a) u t x) =
        fun p : ℝ × ℝ => archLevyDensity p.2 * ∫ x in Ioi (0 : ℝ),
          shiftDifference p.1 x * shiftDifference p.1 (x + p.2) * (u x - u (x + p.2)) ^ 2 := by
      funext p
      show archLevyDensity p.2 *
        (∫ x in Ioi (0 : ℝ), sameSideGroundJump (shiftedGroundState p.1) u p.2 x) = _
      congr 1
      exact setIntegral_congr_fun measurableSet_Ioi fun x _ =>
        sameSideGroundJump_shiftedGroundState p.1 u p.2 x
    rw [e]
    exact ((measurable_archLevyDensity.comp measurable_snd).mul
      (measurable_sameSideShift_prod hu)).aestronglyMeasurable
  rw [integrable_prod_iff' hmeas]
  refine ⟨ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_, ?_⟩
  · show Integrable (fun a => archLevyDensity t *
      ∫ x in Ioi (0 : ℝ), sameSideGroundJump (shiftedGroundState a) u t x)
      (volume.restrict (Ioi 0))
    exact (integrableOn_sameSideIntegral_shiftedGroundState hu huc (le_of_lt ht)).const_mul _
  · have hdom : Integrable (fun t => (riemannKernelReal 0 * (L ^ 2 + 4 * M ^ 2) * R) *
        (archLevyDensity t * t)) (volume.restrict (Ioi 0)) :=
      integrableOn_archLevyDensity_mul_id.const_mul _
    have hint : Integrable (fun t => archLevyDensity t * averagedSameSideShift u t)
        (volume.restrict (Ioi 0)) := by
      refine hdom.mono' (measurable_archLevyDensity.mul
        (measurable_averagedSameSideShift hu)).aestronglyMeasurable
        (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_)
      have ht0 : 0 < t := ht
      have hL' := archLevyDensity_pos ht0
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hL'.le
        (averagedSameSideShift_nonneg u ht0.le))]
      calc archLevyDensity t * averagedSameSideShift u t
          ≤ archLevyDensity t * (riemannKernelReal 0 * (L ^ 2 + 4 * M ^ 2) * t * R) :=
            mul_le_mul_of_nonneg_left
              (averagedSameSideShift_le_linear hR hM hsupp hL ht0) hL'.le
        _ = _ := by ring
    refine hint.congr (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_)
    have ht0 : 0 < t := ht
    have hL' := archLevyDensity_pos ht0
    show archLevyDensity t * averagedSameSideShift u t = ∫ a in Ioi (0 : ℝ),
      ‖archLevyDensity t * ∫ x in Ioi (0 : ℝ), sameSideGroundJump (shiftedGroundState a) u t x‖
    rw [← integral_Ioi_sameSideIntegral_shiftedGroundState hu huc ht0.le, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun a ha => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hL'.le
      (integral_sameSide_shiftedGroundState_nonneg ha u ht0.le))]

theorem integral_Ioi_archSameSide_shiftedGroundState {u : ℝ → ℝ} {M R L : ℝ} (hu : Continuous u)
    (huc : HasCompactSupport u) (hR : 0 ≤ R) (hM : ∀ x, |u x| ≤ M)
    (hsupp : ∀ x, R < |x| → u x = 0)
    (hL : ∀ x ∈ Icc (-R - 1) (R + 1), ∀ y ∈ Icc (-R - 1) (R + 1), |u y - u x| ≤ L * |y - x|) :
    (∫ a in Ioi (0 : ℝ), ∫ t in Ioi (0 : ℝ), archLevyDensity t *
        ∫ x in Ioi (0 : ℝ), sameSideGroundJump (shiftedGroundState a) u t x) =
      ∫ t in Ioi (0 : ℝ), archLevyDensity t * averagedSameSideShift u t := by
  rw [integral_integral_swap (integrable_archLevy_sameSide_prod hu huc hR hM hsupp hL)]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  rw [← integral_Ioi_sameSideIntegral_shiftedGroundState hu huc (le_of_lt ht), ← integral_const_mul]

theorem integrableOn_archSameSide_shiftedGroundState {u : ℝ → ℝ} {M R L : ℝ} (hu : Continuous u)
    (huc : HasCompactSupport u) (hR : 0 ≤ R) (hM : ∀ x, |u x| ≤ M)
    (hsupp : ∀ x, R < |x| → u x = 0)
    (hL : ∀ x ∈ Icc (-R - 1) (R + 1), ∀ y ∈ Icc (-R - 1) (R + 1), |u y - u x| ≤ L * |y - x|) :
    IntegrableOn (fun a => ∫ t in Ioi (0 : ℝ), archLevyDensity t *
      ∫ x in Ioi (0 : ℝ), sameSideGroundJump (shiftedGroundState a) u t x) (Ioi 0) :=
  (integrable_archLevy_sameSide_prod hu huc hR hM hsupp hL).integral_prod_left

/-! ### The prime part of the same-side energy -/

theorem summable_atom_mul_averagedSameSideShift {u : ℝ → ℝ} {M R : ℝ} (hR : 0 ≤ R)
    (hM : ∀ x, |u x| ≤ M) (hsupp : ∀ x, R < |x| → u x = 0) :
    Summable fun n : ℕ => vonMangoldtAtom n * averagedSameSideShift u (Real.log n) := by
  refine (summable_atom_mul_kernel_half.mul_left (4 * M ^ 2 * R)).of_nonneg_of_le
    (fun n => mul_nonneg (vonMangoldtAtom_nonneg n)
      (averagedSameSideShift_nonneg u (Real.log_natCast_nonneg n))) (fun n => ?_)
  calc vonMangoldtAtom n * averagedSameSideShift u (Real.log n)
      ≤ vonMangoldtAtom n * (4 * M ^ 2 * riemannKernelReal (Real.log n / 2) * R) :=
        mul_le_mul_of_nonneg_left
          (averagedSameSideShift_le_decay hR hM hsupp (Real.log_natCast_nonneg n))
          (vonMangoldtAtom_nonneg n)
    _ = 4 * M ^ 2 * R * (vonMangoldtAtom n * riemannKernelReal (Real.log n / 2)) := by ring

theorem integrable_atom_sameSide_term {u : ℝ → ℝ} (hu : Continuous u) (huc : HasCompactSupport u)
    (n : ℕ) :
    Integrable (fun a => vonMangoldtAtom n * ∫ x in Ioi (0 : ℝ),
      sameSideGroundJump (shiftedGroundState a) u (Real.log n) x) (volume.restrict (Ioi 0)) :=
  (integrableOn_sameSideIntegral_shiftedGroundState hu huc (Real.log_natCast_nonneg n)).const_mul _

theorem integral_Ioi_atom_sameSide_term {u : ℝ → ℝ} (hu : Continuous u) (huc : HasCompactSupport u)
    (n : ℕ) :
    (∫ a in Ioi (0 : ℝ), vonMangoldtAtom n * ∫ x in Ioi (0 : ℝ),
      sameSideGroundJump (shiftedGroundState a) u (Real.log n) x) =
      vonMangoldtAtom n * averagedSameSideShift u (Real.log n) := by
  rw [integral_const_mul,
    integral_Ioi_sameSideIntegral_shiftedGroundState hu huc (Real.log_natCast_nonneg n)]

theorem integral_Ioi_norm_atom_sameSide_term {u : ℝ → ℝ} (hu : Continuous u)
    (huc : HasCompactSupport u) (n : ℕ) :
    (∫ a in Ioi (0 : ℝ), ‖vonMangoldtAtom n * ∫ x in Ioi (0 : ℝ),
      sameSideGroundJump (shiftedGroundState a) u (Real.log n) x‖) =
      vonMangoldtAtom n * averagedSameSideShift u (Real.log n) := by
  rw [← integral_Ioi_atom_sameSide_term hu huc n]
  refine setIntegral_congr_fun measurableSet_Ioi fun a ha => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (vonMangoldtAtom_nonneg n)
    (integral_sameSide_shiftedGroundState_nonneg ha u (Real.log_natCast_nonneg n)))]

theorem integral_Ioi_primeSameSide_shiftedGroundState {u : ℝ → ℝ} {M R : ℝ} (hu : Continuous u)
    (huc : HasCompactSupport u) (hR : 0 ≤ R) (hM : ∀ x, |u x| ≤ M)
    (hsupp : ∀ x, R < |x| → u x = 0) :
    (∫ a in Ioi (0 : ℝ), ∑' n : ℕ, vonMangoldtAtom n * ∫ x in Ioi (0 : ℝ),
        sameSideGroundJump (shiftedGroundState a) u (Real.log n) x) =
      ∑' n : ℕ, vonMangoldtAtom n * averagedSameSideShift u (Real.log n) := by
  have hF_sum : Summable fun n : ℕ => ∫ a in Ioi (0 : ℝ), ‖vonMangoldtAtom n *
      ∫ x in Ioi (0 : ℝ), sameSideGroundJump (shiftedGroundState a) u (Real.log n) x‖ :=
    (summable_atom_mul_averagedSameSideShift hR hM hsupp).congr fun n =>
      (integral_Ioi_norm_atom_sameSide_term hu huc n).symm
  rw [← integral_tsum_of_summable_integral_norm (integrable_atom_sameSide_term hu huc) hF_sum]
  exact tsum_congr fun n => integral_Ioi_atom_sameSide_term hu huc n

theorem integrableOn_primeSameSide_shiftedGroundState {u : ℝ → ℝ} {M R : ℝ} (hu : Continuous u)
    (huc : HasCompactSupport u) (hR : 0 ≤ R) (hM : ∀ x, |u x| ≤ M)
    (hsupp : ∀ x, R < |x| → u x = 0) :
    IntegrableOn (fun a => ∑' n : ℕ, vonMangoldtAtom n * ∫ x in Ioi (0 : ℝ),
      sameSideGroundJump (shiftedGroundState a) u (Real.log n) x) (Ioi 0) := by
  refine integrable_tsum_of_nonneg (integrable_atom_sameSide_term hu huc) (fun n => ?_) ?_
  · exact ae_restrict_of_forall_mem measurableSet_Ioi fun a ha =>
      mul_nonneg (vonMangoldtAtom_nonneg n)
        (integral_sameSide_shiftedGroundState_nonneg ha u (Real.log_natCast_nonneg n))
  · exact (summable_atom_mul_averagedSameSideShift hR hM hsupp).congr fun n =>
      (integral_Ioi_atom_sameSide_term hu huc n).symm

/-! ### The averaged same-side energy -/

/-- The averaged same-side energy `∫ dm(t) ∫_{x>0} K(x, x+t) (u(x) − u(x+t))² dx`. -/
def averagedSameSideEnergy (u : ℝ → ℝ) : ℝ :=
  (∫ t in Ioi (0 : ℝ), archLevyDensity t * averagedSameSideShift u t) +
    ∑' n : ℕ, vonMangoldtAtom n * averagedSameSideShift u (Real.log n)

theorem integrableOn_sameSideEnergy_shiftedGroundState {u : ℝ → ℝ} (hu : ContDiff ℝ 1 u)
    (huc : HasCompactSupport u) :
    IntegrableOn (fun a => sameSideEnergy (shiftedGroundState a) u) (Ioi 0) := by
  obtain ⟨R, hR1, hsupp⟩ := exists_support_radius huc
  obtain ⟨M, hM'⟩ := hu.continuous.bounded_above_of_compact_support huc
  have hM : ∀ x, |u x| ≤ M := fun x => by
    rw [← Real.norm_eq_abs]
    exact hM' x
  obtain ⟨L, _, hL⟩ := exists_lipschitz_bound_on_Icc hu (-R - 1) (R + 1)
  have hR0 : 0 ≤ R := by linarith
  refine ((integrableOn_archSameSide_shiftedGroundState hu.continuous huc hR0 hM hsupp hL).add
    (integrableOn_primeSameSide_shiftedGroundState hu.continuous huc hR0 hM hsupp)).congr
    (Eventually.of_forall fun a => ?_)
  rfl

/-- **The shift average of the same-side energy.** -/
theorem integral_Ioi_sameSideEnergy_shiftedGroundState {u : ℝ → ℝ} (hu : ContDiff ℝ 1 u)
    (huc : HasCompactSupport u) :
    (∫ a in Ioi (0 : ℝ), sameSideEnergy (shiftedGroundState a) u) = averagedSameSideEnergy u := by
  obtain ⟨R, hR1, hsupp⟩ := exists_support_radius huc
  obtain ⟨M, hM'⟩ := hu.continuous.bounded_above_of_compact_support huc
  have hM : ∀ x, |u x| ≤ M := fun x => by
    rw [← Real.norm_eq_abs]
    exact hM' x
  obtain ⟨L, _, hL⟩ := exists_lipschitz_bound_on_Icc hu (-R - 1) (R + 1)
  have hR0 : 0 ≤ R := by linarith
  unfold sameSideEnergy averagedSameSideEnergy
  rw [integral_add (integrableOn_archSameSide_shiftedGroundState hu.continuous huc hR0 hM hsupp hL)
    (integrableOn_primeSameSide_shiftedGroundState hu.continuous huc hR0 hM hsupp),
    integral_Ioi_archSameSide_shiftedGroundState hu.continuous huc hR0 hM hsupp hL,
    integral_Ioi_primeSameSide_shiftedGroundState hu.continuous huc hR0 hM hsupp]

/-! ### The averaged source -/

theorem integrable_source_prod {u : ℝ → ℝ} (hu : Continuous u) (huc : HasCompactSupport u) :
    Integrable (Function.uncurry fun a x =>
        4 * Real.sinh (a / 2) * shiftDifference a x * Real.sinh (x / 2) * u x ^ 2)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hcont : Continuous (Function.uncurry fun a x : ℝ =>
      4 * Real.sinh (a / 2) * shiftDifference a x * Real.sinh (x / 2) * u x ^ 2) :=
    (((continuous_const.mul (Real.continuous_sinh.comp (continuous_fst.div_const 2))).mul
      continuous_shiftDifference_uncurry).mul
      (Real.continuous_sinh.comp (continuous_snd.div_const 2))).mul ((hu.comp continuous_snd).pow 2)
  rw [integrable_prod_iff' hcont.aestronglyMeasurable]
  refine ⟨Eventually.of_forall fun x => ?_, ?_⟩
  · show Integrable (fun a => 4 * Real.sinh (a / 2) * shiftDifference a x * Real.sinh (x / 2) *
      u x ^ 2) (volume.restrict (Ioi 0))
    exact ((integrable_sinh_mul_shiftDifference x).mul_const _).integrableOn
  have hK : Integrable (fun x => (2 * Real.sinh (x / 2) ^ 2) * u x ^ 2)
      (volume.restrict (Ioi (0 : ℝ))) :=
    integrableOn_continuous_mul_sq
      (continuous_const.mul ((Real.continuous_sinh.comp (continuous_id.div_const 2)).pow 2)) hu huc _
  refine hK.congr (ae_restrict_of_forall_mem measurableSet_Ioi fun x hx => ?_)
  show 2 * Real.sinh (x / 2) ^ 2 * u x ^ 2 = ∫ a in Ioi (0 : ℝ),
    ‖4 * Real.sinh (a / 2) * shiftDifference a x * Real.sinh (x / 2) * u x ^ 2‖
  rw [← integral_Ioi_sinh_mul_shiftDifference x, ← integral_mul_const]
  refine setIntegral_congr_fun measurableSet_Ioi fun a ha => ?_
  have hx0 : 0 < x := hx
  have ha0 : 0 < a := ha
  rw [Real.norm_eq_abs, abs_of_nonneg]
  exact mul_nonneg (mul_nonneg (mul_nonneg
    (mul_nonneg (by norm_num) (Real.sinh_nonneg_iff.mpr (by positivity)))
    (shiftDifference_nonneg_of_nonneg ha0.le hx0.le))
    (Real.sinh_nonneg_iff.mpr (by positivity))) (sq_nonneg _)

theorem source_eq_integral (u : ℝ → ℝ) (a : ℝ) :
    4 * Real.sinh (a / 2) * (∫ x in Ioi (0 : ℝ), u x ^ 2 * shiftDifference a x * Real.sinh (x / 2)) =
      ∫ x in Ioi (0 : ℝ), 4 * Real.sinh (a / 2) * shiftDifference a x * Real.sinh (x / 2) * u x ^ 2 := by
  rw [← integral_const_mul]
  exact setIntegral_congr_fun measurableSet_Ioi fun x _ => by ring

/-- **The shift average of the source.** -/
theorem integral_Ioi_source_shiftedGroundState {u : ℝ → ℝ} (hu : Continuous u)
    (huc : HasCompactSupport u) :
    (∫ a in Ioi (0 : ℝ), 4 * Real.sinh (a / 2) *
        ∫ x in Ioi (0 : ℝ), u x ^ 2 * shiftDifference a x * Real.sinh (x / 2)) =
      2 * ∫ x in Ioi (0 : ℝ), u x ^ 2 * Real.sinh (x / 2) ^ 2 := by
  rw [integral_congr_ae (Eventually.of_forall (source_eq_integral u)),
    integral_integral_swap (integrable_source_prod hu huc), ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  rw [integral_mul_const, integral_Ioi_sinh_mul_shiftDifference]
  ring

theorem integrableOn_source_shiftedGroundState {u : ℝ → ℝ} (hu : Continuous u)
    (huc : HasCompactSupport u) :
    IntegrableOn (fun a => 4 * Real.sinh (a / 2) *
      ∫ x in Ioi (0 : ℝ), u x ^ 2 * shiftDifference a x * Real.sinh (x / 2)) (Ioi 0) := by
  refine (integrable_source_prod hu huc).integral_prod_left.congr
    (Eventually.of_forall fun a => ?_)
  exact (source_eq_integral u a).symm

end GaloisForLFunctions.ArithmeticCriticalityTheory

end
