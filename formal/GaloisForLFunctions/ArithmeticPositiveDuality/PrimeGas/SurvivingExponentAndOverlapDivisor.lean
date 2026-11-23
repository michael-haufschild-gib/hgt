import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.TraceExponents.FullFrontier
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.PartitionConservationRigidity
import GaloisForLFunctions.RHTower.SalemFermiModeIntegral

/-!
# Direct surviving-partition trace exponents, vertical blindness of self-overlap, and the dyadic overlap divisor

Two structural decoupled mechanisms prevented the existing prime-gas conservation detectors from
seeing the zero locus of `continued s = (2^s - 1) ζ(s)`:

1. **Vertical phase covariance of diagonal self-overlap (`overlap_vertical_shift_eq`,
   `norm_self_overlap_vertical_invariant`,
   `exists_nonvanishing_real_with_identical_self_overlap`)**:
   In `ComplementaryHalves.overlap t j a s s v = conj (reading t j a s v) * reading t j a s (C v)`,
   conjugating the first factor cancels the imaginary exponent `v^{± i Im s}` at every `v > 0`:
   `overlap t j a (s + i τ) (s + i τ) v = C^{i τ} * overlap t j a s s v`.
   Since `continued σ ≠ 0` for every real `σ ∈ (0, 1)`, every open-strip point `s` shares its exact
   positive-time self-overlap norm trajectory with the nonvanishing real parameter `σ = Re s`.

2. **Haar-`L^2` reading frontier and the dyadic half-time overlap integral for `continued`
   (`sqrt_kernel_le_cutoffHeat_and_le`, `integrableOn_norm_sq_reading_haar_iff`,
   `split_isometric_iff_reading_haar_frontier`, `integrableOn_holomorphicOverlap_div_iff`,
   `integral_dyadicOverlapContrast_div_eq`, `integral_holomorphicOverlap_div_eq`,
   `continued_eq_zero_iff_integral_dyadicOverlapContrast_eq_zero`)**:
   Pinching `cutoffHeat` between `√kernel(C, a, v)` and `√kernel(C, a, v/C)` identifies `Re s = 1/2`
   (isometric `split s`) as the exact topological frontier of `L^2((0, ∞), dv/v)` normalizability of
   `reading t j a s`. Replacing the Hermitian diagonal `(s, s)` of `overlap` by the anti-conjugate
   half-time slice `(conj (s/2), s/2)` at `a_* = BalancedShift.center t j` defines
   `holomorphicOverlap t j s v`, whose Haar integral converges iff `1 < Re s` (matching the Gibbs
   trace abscissa) to `C^{s/2} Γ(s) continued s`. Its dyadic contrast
   `dyadicOverlapContrast t j s v = holomorphicOverlap t j s v - 2^{1-s} holomorphicOverlap t j s (2v)`
   cancels the high-temperature `v⁻¹` pole via the Boson–Fermion identity
   `(2 sinh(v/2))⁻¹ - (sinh v)⁻¹ = (exp(v/2) + 1)⁻¹ - (exp v + 1)⁻¹`, giving an unrenormalized Haar
   integral across all `Re s > 0` (`s ≠ 1`) equal to `C^{s/2} (1 - 2^{1-s}) Γ(s) continued s`,
   which vanishes on `{0 < Re s ∧ Re s ≠ 1}` if and only if `continued s = 0`.

3. **Direct surviving-partition trace exponents and conservation criteria
   (`jointSurvivingPartition`, `jointSurvivingTracePowers`,
   `exists_small_trace_jointSurviving_violation`,
   `nonempty_jointSurvivingTracePowers_iff_continued_eq_zero`,
   `mem_jointSurvivingTracePowers_four_iff`, `isLeast_jointSurvivingTracePowers_four_iff`,
   `joint_partition_zero_least_surviving_power_four_below_eightyFour_and_half`,
   `rh_iff_surviving_exponent_four_at_dyadicOverlap_zeros_above_eightyFour_and_half`)**:
   `admissibleTracePowers` (`FullFrontier`) subtracted `ζ(z)` before comparing against
   `traceLoss (projected P)`. Testing the unsubtracted `jointSurvivingPartition b z` across positive
   conserving propagators of missing dimension `r + 1` yields `jointSurvivingTracePowers (r + 1) z`:
   it is empty whenever `continued z ≠ 0` (witnessed by arbitrarily small fourth-trace-loss
   conserving omissions approaching `hotEdge (r + 1)`), equals `[max(1, 2 / Re z), ∞)` when
   `continued z = 0`, contains `4` iff `continued z = 0 ∧ 1/2 ≤ Re z`, and has least element `4`
   iff `continued z = 0` and `split z` is isometric.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas

open Filter MeasureTheory Set Topology
open InverseSpectrum.ShellMixing
open AntipodalSpectrum AntipodalSpectrum.ComplementaryHalves
open scoped ComplexConjugate Topology

/-! ### Part 1: Vertical phase covariance and real-anchor blindness of diagonal self-overlap -/

/-- Positive-time vertical phase covariance of the diagonal complementary overlap: shifting `s`
vertically by `i τ` multiplies `overlap t j a s s v` by the `v`-independent unit phase `C^{i τ}`. -/
theorem overlap_vertical_shift_eq (t : ExceptionalTime) (j : ℕ) (a : ℝ) (s : ℂ) (τ : ℝ)
    {v : ℝ} (hv : 0 < v) :
    ComplementaryHalves.overlap t j a (s + (τ : ℂ) * Complex.I) (s + (τ : ℂ) * Complex.I) v =
      ((tailRadix t j).val : ℂ) ^ ((τ : ℂ) * Complex.I) *
        ComplementaryHalves.overlap t j a s s v := by
  set z : ℂ := (τ : ℂ) * Complex.I
  have hC_pos : (0 : ℝ) < (tailRadix t j).val := Nat.cast_pos.mpr (tailRadix t j).pos
  have hCv_pos : 0 < ((tailRadix t j).val : ℝ) * v := mul_pos hC_pos hv
  have hv_ne : (v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hv.ne'
  have hCv_ne : ((((tailRadix t j).val : ℝ) * v : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hCv_pos.ne'
  have hconj_unit : conj ((v : ℂ) ^ z) * (v : ℂ) ^ z = 1 := by
    rw [Complex.cpow_def_of_ne_zero hv_ne, ← Complex.ofReal_log hv.le, ← Complex.exp_conj,
      ← Complex.exp_add]
    suffices h0 : conj ((Real.log v : ℂ) * z) + (Real.log v : ℂ) * z = 0 by
      rw [h0, Complex.exp_zero]
    simp [z]
  have hCv_split : ((((tailRadix t j).val : ℝ) * v : ℝ) : ℂ) ^ z =
      ((tailRadix t j).val : ℂ) ^ z * (v : ℂ) ^ z := by
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hC_pos.le hv.le, Complex.ofReal_natCast]
  unfold ComplementaryHalves.overlap ComplementaryHalves.reading
  rw [Complex.cpow_add _ _ hv_ne, Complex.cpow_add _ _ hCv_ne, hCv_split]
  simp only [map_mul]
  linear_combination
    (((tailRadix t j).val : ℂ) ^ z * conj ((v : ℂ) ^ s) * conj (cutoffHeat t j a v : ℂ) *
      ((((tailRadix t j).val : ℝ) * v : ℝ) : ℂ) ^ s *
      (cutoffHeat t j a (((tailRadix t j).val : ℝ) * v) : ℂ)) * hconj_unit

/-- The positive-time norm of `overlap t j a s s v` is strictly invariant under vertical shifts. -/
theorem norm_self_overlap_vertical_invariant (t : ExceptionalTime) (j : ℕ) (a : ℝ) (s : ℂ)
    (τ : ℝ) {v : ℝ} (hv : 0 < v) :
    ‖ComplementaryHalves.overlap t j a (s + (τ : ℂ) * Complex.I) (s + (τ : ℂ) * Complex.I) v‖ =
      ‖ComplementaryHalves.overlap t j a s s v‖ := by
  have hC_pos : (0 : ℝ) < (tailRadix t j).val := Nat.cast_pos.mpr (tailRadix t j).pos
  rw [overlap_vertical_shift_eq t j a s τ hv, norm_mul,
    show ((tailRadix t j).val : ℂ) = (((tailRadix t j).val : ℝ) : ℂ) by exact
      (Complex.ofReal_natCast _).symm,
    Complex.norm_cpow_eq_rpow_re_of_pos hC_pos]
  have hre : ((τ : ℂ) * Complex.I).re = 0 := by simp
  rw [hre, Real.rpow_zero, one_mul]

/-- **Real-anchor indistinguishability of diagonal self-overlap:** for every open-strip parameter
`s` (`0 < Re s < 1`), the real point `σ = Re s ∈ (0, 1)` satisfies `continued σ ≠ 0` yet has the
identical positive-time self-overlap norm function `v ↦ ‖overlap t j a σ σ v‖` (and differs in
complex value only by the constant phase `C^{i Im s}`). -/
theorem exists_nonvanishing_real_with_identical_self_overlap
    (t : ExceptionalTime) (j : ℕ) (a : ℝ) {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    continued (s.re : ℂ) ≠ 0 ∧
      (∀ v : ℝ, 0 < v →
        ComplementaryHalves.overlap t j a s s v =
          ((tailRadix t j).val : ℂ) ^ ((s.im : ℂ) * Complex.I) *
            ComplementaryHalves.overlap t j a (s.re : ℂ) (s.re : ℂ) v) ∧
      (∀ v : ℝ, 0 < v →
        ‖ComplementaryHalves.overlap t j a s s v‖ =
          ‖ComplementaryHalves.overlap t j a (s.re : ℂ) (s.re : ℂ) v‖) := by
  have hζ : riemannZeta (s.re : ℂ) ≠ 0 := _root_.RHTower.riemannZeta_real_strip_ne_zero hs0 hs1
  have hc_ne : continued (s.re : ℂ) ≠ 0 := fun hc0 =>
    hζ ((ComplementaryHalves.positive_zero_iff ⟨(s.re : ℂ), by simpa using hs0⟩).mp hc0)
  have hs_decomp : (s.re : ℂ) + (s.im : ℂ) * Complex.I = s := Complex.re_add_im s
  refine ⟨hc_ne, fun v hv => ?_, fun v hv => ?_⟩
  · simpa only [hs_decomp] using overlap_vertical_shift_eq t j a (s.re : ℂ) s.im hv
  · simpa only [hs_decomp] using norm_self_overlap_vertical_invariant t j a (s.re : ℂ) s.im hv

/-! ### Part 2: Two-sided heat pinch, Haar-`L^2` reading frontier, and the dyadic overlap integral -/

private theorem singleHeat_nonneg (C : Radix) (a : ℝ) {v : ℝ} (_hv : 0 < v) :
    0 ≤ singleHeat C a v :=
  tsum_nonneg fun _ => (Real.exp_pos _).le

private theorem singleHeat_antitone_of_nonneg (C : Radix) {a : ℝ} (ha : 0 ≤ a)
    {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    singleHeat C a v ≤ singleHeat C a u := by
  have hv : 0 < v := hu.trans_le huv
  refine hasSum_le (fun x => ?_) (entry_summable C a ⟨v, hv⟩).hasSum
    (entry_summable C a ⟨u, hu⟩).hasSum
  unfold entry
  apply Real.exp_le_exp.mpr
  have hxa : 0 ≤ (x.val : ℝ) + a := add_nonneg (Nat.cast_nonneg _) ha
  nlinarith

/-- **Two-sided positive-time pinch of `cutoffHeat`:** for `a ≥ 0` and `v > 0`, `cutoffHeat t j a v`
is pinched between `√kernel(C, a, v)` and `√kernel(C, a, v / C)`. -/
theorem sqrt_kernel_le_cutoffHeat_and_le (t : ExceptionalTime) (j : ℕ) {a : ℝ} (ha : 0 ≤ a)
    {v : ℝ} (hv : 0 < v) :
    Real.sqrt (kernel (clockRadix t j) a v) ≤ cutoffHeat t j a v ∧
      cutoffHeat t j a v ≤
        Real.sqrt (kernel (clockRadix t j) a (v / ((tailRadix t j).val : ℝ))) := by
  let C := clockRadix t j
  have hC1 : (1 : ℝ) < (C.val : ℝ) := by exact_mod_cast C.property
  have hC_pos : (0 : ℝ) < (C.val : ℝ) := zero_lt_one.trans hC1
  have hvC_pos : 0 < v / (C.val : ℝ) := div_pos hv hC_pos
  rw [cutoffHeat_eq]
  have hsh_nn : 0 ≤ singleHeat C a v := singleHeat_nonneg C a hv
  refine ⟨?_, ?_⟩
  · have hle : singleHeat C a ((C.val : ℝ) * v) ≤ singleHeat C a v :=
      singleHeat_antitone_of_nonneg C ha hv (by nlinarith)
    have hprod : kernel C a v ≤ singleHeat C a v ^ 2 := by
      rw [← heat_product C a ⟨v, hv⟩, sq]
      exact mul_le_mul_of_nonneg_left hle hsh_nn
    exact (Real.sqrt_le_sqrt hprod).trans_eq (Real.sqrt_sq hsh_nn)
  · have hle : singleHeat C a v ≤ singleHeat C a (v / (C.val : ℝ)) :=
      singleHeat_antitone_of_nonneg C ha hvC_pos (div_le_self hv.le hC1.le)
    have hprod : singleHeat C a v ^ 2 ≤ kernel C a (v / (C.val : ℝ)) := by
      have hp := heat_product C a ⟨v / (C.val : ℝ), hvC_pos⟩
      dsimp only at hp
      rw [mul_div_cancel₀ _ hC_pos.ne'] at hp
      rw [← hp, sq]
      exact mul_le_mul_of_nonneg_right hle hsh_nn
    exact (Real.sqrt_sq hsh_nn).symm.trans_le (Real.sqrt_le_sqrt hprod)

private theorem inv_one_sub_exp_neg_le {v : ℝ} (hv : 0 < v) :
    (1 - Real.exp (-v))⁻¹ ≤ v⁻¹ + 1 := by
  have hden : 0 < 1 - Real.exp (-v) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hv))
  rw [inv_le_iff_one_le_mul₀ hden]
  have hexp : v + 1 ≤ Real.exp v := Real.add_one_le_exp v
  have hmul_pos : 0 < v * Real.exp v := mul_pos hv (Real.exp_pos v)
  have hid : (1 - Real.exp (-v)) * (v⁻¹ + 1) - 1 =
      (Real.exp v - (v + 1)) / (v * Real.exp v) := by
    rw [Real.exp_neg]
    field_simp [hv.ne', (Real.exp_pos v).ne']
    ring
  have hnn : 0 ≤ (Real.exp v - (v + 1)) / (v * Real.exp v) :=
    div_nonneg (sub_nonneg.mpr hexp) hmul_pos.le
  linarith

private theorem integrableOn_exp_neg_mul_rpow {α q : ℝ} (hα : 0 < α) (hq : 0 < q) :
    IntegrableOn (fun v : ℝ => Real.exp (-α * v) * v ^ (q - 1)) (Ioi 0) := by
  have hG : IntegrableOn (fun u : ℝ => Real.exp (-u) * u ^ (q - 1)) (Ioi (α * 0)) := by
    rw [mul_zero]
    exact Real.GammaIntegral_convergent hq
  have hcomp := (integrableOn_Ioi_comp_mul_left_iff
    (fun u : ℝ => Real.exp (-u) * u ^ (q - 1)) 0 hα).mpr hG
  have hpow_pos : 0 < α ^ (q - 1) := Real.rpow_pos_of_pos hα _
  refine IntegrableOn.congr_fun (hcomp.const_mul (α ^ (q - 1))⁻¹) (fun v hv => ?_) measurableSet_Ioi
  rw [Real.mul_rpow hα.le (le_of_lt hv), neg_mul]
  field_simp [hpow_pos.ne']

private theorem integrableOn_rpow_mul_kernel_iff (C : Radix) {a : ℝ} (ha : 0 < a) (p : ℝ) :
    IntegrableOn (fun v : ℝ => v ^ p * kernel C a v) (Ioi 0) ↔ 0 < p := by
  let α : ℝ := ((C.val : ℝ) + 1) * a
  have hα : 0 < α := mul_pos (by positivity) ha
  constructor
  · intro hint
    have hint_Ioo : IntegrableOn (fun v : ℝ => v ^ p * kernel C a v) (Ioo 0 1) :=
      hint.mono_set Ioo_subset_Ioi_self
    have hmeas_rpow : AEStronglyMeasurable (fun v : ℝ => Real.exp (-α) * v ^ (p - 1))
        (volume.restrict (Ioo 0 1)) := by
      refine (ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioo)
      exact continuousOn_const.mul (continuousOn_id.rpow_const fun x hx => Or.inl hx.1.ne')
    have hlow : IntegrableOn (fun v : ℝ => Real.exp (-α) * v ^ (p - 1)) (Ioo 0 1) := by
      refine hint_Ioo.mono' hmeas_rpow ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
      have hv0 : 0 < v := hv.1
      have hv1 : v < 1 := hv.2
      have hden_pos : 0 < 1 - Real.exp (-v) :=
        sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hv0))
      have hden_le : 1 - Real.exp (-v) ≤ v := by
        linarith [Real.add_one_le_exp (-v)]
      have hinv_ge : v⁻¹ ≤ (1 - Real.exp (-v))⁻¹ := inv_anti₀ hden_pos hden_le
      have hexp_ge : Real.exp (-α) ≤ Real.exp (-v * α) :=
        Real.exp_le_exp.mpr (by nlinarith)
      rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hv0.le _)),
        show v ^ (p - 1) = v ^ p * v⁻¹ by
          rw [sub_eq_add_neg, Real.rpow_add hv0, Real.rpow_neg_one]]
      unfold kernel
      change Real.exp (-α) * (v ^ p * v⁻¹) ≤ v ^ p * (Real.exp (-v * α) / (1 - Real.exp (-v)))
      rw [div_eq_mul_inv, show Real.exp (-α) * (v ^ p * v⁻¹) = v ^ p * (Real.exp (-α) * v⁻¹) by ring]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul hexp_ge hinv_ge (inv_nonneg.mpr hv0.le) (Real.exp_pos _).le)
        (Real.rpow_nonneg hv0.le _)
    have hrpow : IntegrableOn (fun v : ℝ => v ^ (p - 1)) (Ioo 0 1) := by
      refine IntegrableOn.congr_fun (hlow.const_mul (Real.exp α)) (fun v _ => ?_) measurableSet_Ioo
      rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
    have hgt := (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).mp hrpow
    linarith
  · intro hp
    have hcont : ContinuousOn (fun v : ℝ => v ^ p * kernel C a v) (Ioi 0) := by
      refine (continuousOn_id.rpow_const fun x hx => Or.inl (ne_of_gt hx)).mul ?_
      unfold kernel
      refine ContinuousOn.div (by fun_prop) (by fun_prop) fun x hx => ?_
      exact (sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hx))).ne'
    have hdom : IntegrableOn
        (fun v : ℝ => Real.exp (-α * v) * v ^ (p - 1) + Real.exp (-α * v) * v ^ p) (Ioi 0) := by
      refine (integrableOn_exp_neg_mul_rpow hα hp).add ?_
      simpa only [add_sub_cancel_right] using
        integrableOn_exp_neg_mul_rpow hα (by linarith : 0 < p + 1)
    refine hdom.mono' (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    have hv0 : 0 < v := hv
    have hker_nn : 0 ≤ kernel C a v := by
      unfold kernel
      exact div_nonneg (Real.exp_pos _).le
        (sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hv0))).le
    rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg hv0.le _) hker_nn)]
    unfold kernel
    change v ^ p * (Real.exp (-v * α) / (1 - Real.exp (-v))) ≤ _
    calc v ^ p * (Real.exp (-v * α) / (1 - Real.exp (-v)))
        = v ^ p * Real.exp (-α * v) * (1 - Real.exp (-v))⁻¹ := by
          rw [div_eq_mul_inv, show -v * α = -α * v by ring]; ring
      _ ≤ v ^ p * Real.exp (-α * v) * (v⁻¹ + 1) :=
          mul_le_mul_of_nonneg_left (inv_one_sub_exp_neg_le hv0)
            (mul_nonneg (Real.rpow_nonneg hv0.le _) (Real.exp_pos _).le)
      _ = Real.exp (-α * v) * v ^ (p - 1) + Real.exp (-α * v) * v ^ p := by
          rw [show v ^ (p - 1) = v ^ p * v⁻¹ by
            rw [sub_eq_add_neg, Real.rpow_add hv0, Real.rpow_neg_one]]
          ring

/-- **Sharp Haar-`L^2` normalizability threshold of `reading`:** for every `a > 0`,
`v ↦ ‖reading t j a s v‖^2 / v` is integrable on `(0, ∞)` if and only if `1 / 2 < Re s`. -/
theorem integrableOn_norm_sq_reading_haar_iff (t : ExceptionalTime) (j : ℕ) {a : ℝ} (ha : 0 < a)
    (s : ℂ) :
    IntegrableOn (fun v : ℝ => ‖ComplementaryHalves.reading t j a s v‖ ^ 2 / v) (Ioi 0) ↔
      1 / 2 < s.re := by
  let C := clockRadix t j
  have hC_pos : (0 : ℝ) < (tailRadix t j).val := Nat.cast_pos.mpr (tailRadix t j).pos
  have hmeas_ch : Measurable (cutoffHeat t j a) := by
    unfold cutoffHeat
    exact Measurable.tsum fun _ => (by fun_prop : Continuous _).measurable
  have hmeas_rd : AEStronglyMeasurable
      (fun v : ℝ => ‖ComplementaryHalves.reading t j a s v‖ ^ 2 / v)
      (volume.restrict (Ioi 0)) := by
    have h1 : AEStronglyMeasurable (fun v : ℝ => v ^ (2 * s.re - 1))
        (volume.restrict (Ioi 0)) :=
      (continuousOn_id.rpow_const fun x hx => Or.inl (ne_of_gt hx)).aestronglyMeasurable
        measurableSet_Ioi
    have h2 : AEStronglyMeasurable (fun v : ℝ => cutoffHeat t j a v ^ 2)
        (volume.restrict (Ioi 0)) :=
      (hmeas_ch.pow_const 2).aestronglyMeasurable
    refine (h1.mul h2).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    have hv0 : 0 < v := hv
    dsimp only [Pi.mul_apply]
    unfold ComplementaryHalves.reading
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hv0, Complex.norm_real, Real.norm_eq_abs,
      mul_pow, sq_abs, ← Real.rpow_natCast (v ^ s.re) 2, ← Real.rpow_mul hv0.le]
    have hvp : (v ^ (s.re * (2 : ℕ))) / v = v ^ (2 * s.re - 1) := by
      rw [Nat.cast_ofNat, div_eq_mul_inv, ← Real.rpow_neg_one v, ← Real.rpow_add hv0]
      congr 1; ring
    rw [mul_div_right_comm, hvp]
  constructor
  · intro hint
    have hker_int : IntegrableOn (fun v : ℝ => v ^ (2 * s.re - 1) * kernel C a v) (Ioi 0) := by
      have hcont : ContinuousOn (fun v : ℝ => v ^ (2 * s.re - 1) * kernel C a v) (Ioi 0) := by
        refine (continuousOn_id.rpow_const fun x hx => Or.inl (ne_of_gt hx)).mul ?_
        unfold kernel
        exact ContinuousOn.div (by fun_prop) (by fun_prop) fun x hx =>
          (sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hx))).ne'
      refine hint.mono' (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      have hv0 : 0 < v := hv
      have hker_nn : 0 ≤ kernel C a v := by
        unfold kernel
        exact div_nonneg (Real.exp_pos _).le
          (sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hv0))).le
      have hpinch := (sqrt_kernel_le_cutoffHeat_and_le t j ha.le hv0).1
      have hsq : kernel C a v ≤ cutoffHeat t j a v ^ 2 := by
        have h := mul_self_le_mul_self (Real.sqrt_nonneg _) hpinch
        rwa [Real.mul_self_sqrt hker_nn, ← sq] at h
      rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg hv0.le _) hker_nn)]
      unfold ComplementaryHalves.reading
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hv0, Complex.norm_real, Real.norm_eq_abs,
        mul_pow, sq_abs, ← Real.rpow_natCast (v ^ s.re) 2, ← Real.rpow_mul hv0.le,
        mul_div_right_comm, show (v ^ (s.re * (2 : ℕ))) / v = v ^ (2 * s.re - 1) by
          rw [Nat.cast_ofNat, div_eq_mul_inv, ← Real.rpow_neg_one v, ← Real.rpow_add hv0]
          congr 1; ring]
      exact mul_le_mul_of_nonneg_left hsq (Real.rpow_nonneg hv0.le _)
    have hp := (integrableOn_rpow_mul_kernel_iff C ha (2 * s.re - 1)).mp hker_int
    linarith
  · intro hs
    have hp : 0 < 2 * s.re - 1 := by linarith
    have hbase := (integrableOn_rpow_mul_kernel_iff C ha (2 * s.re - 1)).mpr hp
    have hC_inv : 0 < ((tailRadix t j).val : ℝ)⁻¹ := inv_pos.mpr hC_pos
    have hbase' : IntegrableOn
        (fun u : ℝ => u ^ (2 * s.re - 1) * kernel C a u)
        (Ioi (((tailRadix t j).val : ℝ)⁻¹ * 0)) := by
      rwa [mul_zero]
    have hcomp := (integrableOn_Ioi_comp_mul_left_iff
      (fun u : ℝ => u ^ (2 * s.re - 1) * kernel C a u) 0 hC_inv).mpr hbase'
    have hdom : IntegrableOn
        (fun v : ℝ => v ^ (2 * s.re - 1) * kernel C a (v / ((tailRadix t j).val : ℝ)))
        (Ioi 0) := by
      have hc_pos : 0 < (((tailRadix t j).val : ℝ)⁻¹) ^ (2 * s.re - 1) :=
        Real.rpow_pos_of_pos hC_inv _
      refine IntegrableOn.congr_fun
        (hcomp.const_mul ((((tailRadix t j).val : ℝ)⁻¹) ^ (2 * s.re - 1))⁻¹)
        (fun v hv => ?_) measurableSet_Ioi
      rw [Real.mul_rpow hC_inv.le (le_of_lt hv), inv_mul_eq_div]
      field_simp [hc_pos.ne']
    refine hdom.mono' hmeas_rd ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    have hv0 : 0 < v := hv
    have hker_nn : 0 ≤ kernel C a (v / ((tailRadix t j).val : ℝ)) := by
      unfold kernel
      exact div_nonneg (Real.exp_pos _).le
        (sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos (div_pos hv0 hC_pos)))).le
    have hch_nn : 0 ≤ cutoffHeat t j a v := by
      rw [cutoffHeat_eq]; exact singleHeat_nonneg C a hv0
    have hpinch := (sqrt_kernel_le_cutoffHeat_and_le t j ha.le hv0).2
    have hsq : cutoffHeat t j a v ^ 2 ≤ kernel C a (v / ((tailRadix t j).val : ℝ)) := by
      have h := mul_self_le_mul_self hch_nn hpinch
      rwa [Real.mul_self_sqrt hker_nn, ← sq] at h
    rw [Real.norm_of_nonneg (div_nonneg (sq_nonneg _) hv0.le)]
    unfold ComplementaryHalves.reading
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hv0, Complex.norm_real, Real.norm_eq_abs,
      mul_pow, sq_abs, ← Real.rpow_natCast (v ^ s.re) 2, ← Real.rpow_mul hv0.le,
      mul_div_right_comm, show (v ^ (s.re * (2 : ℕ))) / v = v ^ (2 * s.re - 1) by
        rw [Nat.cast_ofNat, div_eq_mul_inv, ← Real.rpow_neg_one v, ← Real.rpow_add hv0]
        congr 1; ring]
    exact mul_le_mul_of_nonneg_left hsq (Real.rpow_nonneg hv0.le _)

/-- **Isometric divisor splitting as the Haar-`L^2` reading frontier:** for every `a > 0`, `split s`
is isometric if and only if `s` lies on the topological frontier of the Haar-`L^2` normalizability
domain of `reading t j a`. -/
theorem split_isometric_iff_reading_haar_frontier (t : ExceptionalTime) (j : ℕ) {a : ℝ}
    (ha : 0 < a) (s : ℂ) :
    (∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split s f x) ↔
      s ∈ frontier {z : ℂ |
        IntegrableOn (fun v : ℝ => ‖ComplementaryHalves.reading t j a z v‖ ^ 2 / v) (Ioi 0)} := by
  have hset : {z : ℂ |
      IntegrableOn (fun v : ℝ => ‖ComplementaryHalves.reading t j a z v‖ ^ 2 / v) (Ioi 0)} =
      {z : ℂ | (1 / 2 : ℝ) < z.re} := by
    ext z; exact integrableOn_norm_sq_reading_haar_iff t j ha z
  rw [split_isometric_iff, hset]
  let U : Set ℂ := {z : ℂ | (1 / 2 : ℝ) < z.re}
  have hU_open : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hU_cl_sub : closure U ⊆ {z : ℂ | (1 / 2 : ℝ) ≤ z.re} :=
    closure_minimal (fun _ hz => show (1 / 2 : ℝ) ≤ _ from le_of_lt hz)
      (isClosed_le continuous_const Complex.continuous_re)
  constructor
  · intro hs_eq
    rw [frontier, hU_open.interior_eq]
    refine ⟨?_, fun hgt => (show (1 / 2 : ℝ) < s.re from hgt).ne hs_eq.symm⟩
    have htend : Tendsto (fun n : ℕ => s + (((1 / ((n : ℝ) + 1) : ℝ) : ℂ))) atTop (𝓝 s) := by
      have h0 : Tendsto (fun n : ℕ => (((1 / ((n : ℝ) + 1) : ℝ) : ℂ))) atTop (𝓝 0) :=
        (Complex.continuous_ofReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
      simpa only [add_zero] using tendsto_const_nhds.add h0
    refine mem_closure_of_tendsto htend (Eventually.of_forall fun n => ?_)
    show (1 / 2 : ℝ) < (s + (((1 / ((n : ℝ) + 1) : ℝ) : ℂ))).re
    rw [Complex.add_re, Complex.ofReal_re, hs_eq]
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := div_pos one_pos (by positivity)
    linarith
  · intro hmem
    rw [frontier, hU_open.interior_eq] at hmem
    have hle : (1 / 2 : ℝ) ≤ s.re := hU_cl_sub hmem.1
    have hnot : ¬ (1 / 2 : ℝ) < s.re := hmem.2
    linarith

/-- Centered anti-conjugate half-time slice of `ComplementaryHalves.overlap`: replacing `(s, s)` by
`(conj (s / 2), s / 2)` at `BalancedShift.center t j` removes conjugation on `(0, ∞)` and restores
holomorphy in `s`. -/
def holomorphicOverlap (t : ExceptionalTime) (j : ℕ) (s : ℂ) (v : ℝ) : ℂ :=
  ComplementaryHalves.overlap t j (BalancedShift.center t j) (conj (s / 2)) (s / 2) v

/-- Dyadic contrast of `holomorphicOverlap` that cancels the high-temperature `v⁻¹` pole at `v = 0`
without subtracting any explicit boundary counterterm. -/
def dyadicOverlapContrast (t : ExceptionalTime) (j : ℕ) (s : ℂ) (v : ℝ) : ℂ :=
  holomorphicOverlap t j s v - (2 : ℂ) ^ (1 - s) * holomorphicOverlap t j s (2 * v)

private theorem kernel_center_eq_inv_two_sinh (t : ExceptionalTime) (j : ℕ) {v : ℝ} (hv : 0 < v) :
    kernel (clockRadix t j) (BalancedShift.center t j) v = 1 / (2 * Real.sinh (v / 2)) := by
  have h1 := heat_product (clockRadix t j) (ComplementaryHalves.midpoint (clockRadix t j)) ⟨v, hv⟩
  have h2 := centered_heat_product (clockRadix t j) ⟨v, hv⟩
  exact h1.symm.trans h2

/-- Positive-time factorization and modulus coupling of `holomorphicOverlap`:
1. `holomorphicOverlap t j s v` is the unconjugated product of complementary half-time readings;
2. `holomorphicOverlap t j s v = C^{s / 2} v^s / (2 sinh(v / 2))`;
3. `‖holomorphicOverlap t j s v‖^2 = kernel C a_* v * ‖overlap t j a_* s s v‖`. -/
theorem holomorphicOverlap_eq_mul_reading_and_norm_sq (t : ExceptionalTime) (j : ℕ) (s : ℂ)
    {v : ℝ} (hv : 0 < v) :
    holomorphicOverlap t j s v =
        ComplementaryHalves.reading t j (BalancedShift.center t j) (s / 2) v *
          ComplementaryHalves.reading t j (BalancedShift.center t j) (s / 2)
            (((tailRadix t j).val : ℝ) * v) ∧
      holomorphicOverlap t j s v =
        ((tailRadix t j).val : ℂ) ^ (s / 2) * (v : ℂ) ^ s *
          (((1 / (2 * Real.sinh (v / 2)) : ℝ) : ℂ)) ∧
      ‖holomorphicOverlap t j s v‖ ^ 2 =
        kernel (clockRadix t j) (BalancedShift.center t j) v *
          ‖ComplementaryHalves.overlap t j (BalancedShift.center t j) s s v‖ := by
  set a₀ := BalancedShift.center t j
  have hC_pos : (0 : ℝ) < (tailRadix t j).val := Nat.cast_pos.mpr (tailRadix t j).pos
  have hv_ne : (v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hv.ne'
  have hconj_rd : conj (ComplementaryHalves.reading t j a₀ (conj (s / 2)) v) =
      ComplementaryHalves.reading t j a₀ (s / 2) v := by
    unfold ComplementaryHalves.reading
    rw [map_mul, Complex.conj_ofReal, Complex.cpow_def_of_ne_zero hv_ne, ← Complex.ofReal_log hv.le,
      ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_conj,
      Complex.ofReal_log hv.le, ← Complex.cpow_def_of_ne_zero hv_ne]
  have h1 : holomorphicOverlap t j s v =
      ComplementaryHalves.reading t j a₀ (s / 2) v *
        ComplementaryHalves.reading t j a₀ (s / 2) (((tailRadix t j).val : ℝ) * v) := by
    unfold holomorphicOverlap ComplementaryHalves.overlap
    rw [hconj_rd]
  have h2 : holomorphicOverlap t j s v =
      ((tailRadix t j).val : ℂ) ^ (s / 2) * (v : ℂ) ^ s *
        (((1 / (2 * Real.sinh (v / 2)) : ℝ) : ℂ)) := by
    rw [h1]
    unfold ComplementaryHalves.reading
    have hCv_split : ((((tailRadix t j).val : ℝ) * v : ℝ) : ℂ) ^ (s / 2) =
        ((tailRadix t j).val : ℂ) ^ (s / 2) * (v : ℂ) ^ (s / 2) := by
      rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hC_pos.le hv.le,
        Complex.ofReal_natCast]
    have hv_sq : (v : ℂ) ^ (s / 2) * (v : ℂ) ^ (s / 2) = (v : ℂ) ^ s := by
      rw [← Complex.cpow_add _ _ hv_ne, add_halves]
    have hprod : (cutoffHeat t j a₀ v : ℂ) *
        (cutoffHeat t j a₀ (((tailRadix t j).val : ℝ) * v) : ℂ) =
        (((1 / (2 * Real.sinh (v / 2)) : ℝ) : ℂ)) := by
      rw [← Complex.ofReal_mul, physical_heat_product t j a₀ ⟨v, hv⟩,
        kernel_center_eq_inv_two_sinh t j hv]
    calc ((v : ℂ) ^ (s / 2) * (cutoffHeat t j a₀ v : ℂ)) *
            ((((((tailRadix t j).val : ℝ) * v : ℝ) : ℂ)) ^ (s / 2) *
              (cutoffHeat t j a₀ (((tailRadix t j).val : ℝ) * v) : ℂ))
        = ((tailRadix t j).val : ℂ) ^ (s / 2) * ((v : ℂ) ^ (s / 2) * (v : ℂ) ^ (s / 2)) *
            ((cutoffHeat t j a₀ v : ℂ) *
              (cutoffHeat t j a₀ (((tailRadix t j).val : ℝ) * v) : ℂ)) := by
          rw [hCv_split]; ring
      _ = ((tailRadix t j).val : ℂ) ^ (s / 2) * (v : ℂ) ^ s *
            (((1 / (2 * Real.sinh (v / 2)) : ℝ) : ℂ)) := by
          rw [hv_sq, hprod]
  refine ⟨h1, h2, ?_⟩
  have hker_eq := kernel_center_eq_inv_two_sinh t j hv
  have hker_pos : 0 < kernel (clockRadix t j) a₀ v := by
    unfold kernel
    exact div_pos (Real.exp_pos _) (sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hv)))
  rw [h2, ← hker_eq, norm_self_overlap_eq t j a₀ s hv, norm_mul, norm_mul,
    show ((tailRadix t j).val : ℂ) = (((tailRadix t j).val : ℝ) : ℂ) by exact
      (Complex.ofReal_natCast _).symm,
    Complex.norm_cpow_eq_rpow_re_of_pos hC_pos,
    Complex.norm_cpow_eq_rpow_re_of_pos hv,
    Complex.norm_real, Real.norm_of_nonneg hker_pos.le]
  have hre_half : (s / 2).re = s.re / 2 := by simp
  have hC_sq : (((tailRadix t j).val : ℝ) ^ (s.re / 2)) ^ 2 =
      ((tailRadix t j).val : ℝ) ^ s.re := by
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hC_pos.le, Nat.cast_ofNat]
    congr 1; ring
  have hv_pow : (v ^ s.re) ^ 2 = v * v ^ (2 * s.re - 1) := by
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hv.le, Nat.cast_ofNat,
      show s.re * 2 = 1 + (2 * s.re - 1) by ring, Real.rpow_add hv, Real.rpow_one]
  rw [hre_half, mul_pow, mul_pow, hC_sq, hv_pow]
  ring

/-- **Haar integrability threshold of unsubtracted `holomorphicOverlap`:**
`v ↦ holomorphicOverlap t j s v / v` is integrable on `(0, ∞)` if and only if `1 < Re s`,
matching the Gibbs trace abscissa `JointPartition.absolute_iff`. -/
theorem integrableOn_holomorphicOverlap_div_iff (t : ExceptionalTime) (j : ℕ) (s : ℂ) :
    IntegrableOn (fun v : ℝ => holomorphicOverlap t j s v / (v : ℂ)) (Ioi 0) ↔ 1 < s.re := by
  let C := clockRadix t j
  let a₀ := BalancedShift.center t j
  have ha₀ : 0 < a₀ := by
    change 0 < ComplementaryHalves.midpoint C
    unfold ComplementaryHalves.midpoint
    exact div_pos one_pos (by positivity)
  have hC_pos : (0 : ℝ) < (tailRadix t j).val := Nat.cast_pos.mpr (tailRadix t j).pos
  have hc_pos : 0 < ((tailRadix t j).val : ℝ) ^ (s.re / 2) := Real.rpow_pos_of_pos hC_pos _
  have hcont : ContinuousOn (fun v : ℝ => holomorphicOverlap t j s v / (v : ℂ)) (Ioi 0) := by
    refine ContinuousOn.congr (f := fun v : ℝ =>
      (((tailRadix t j).val : ℂ) ^ (s / 2) * (v : ℂ) ^ s *
        (((kernel C a₀ v : ℝ) : ℂ))) / (v : ℂ)) ?_ (fun v hv => ?_)
    · refine ContinuousOn.div ?_ (Complex.continuous_ofReal.continuousOn)
        (fun x hx => Complex.ofReal_ne_zero.mpr (ne_of_gt hx))
      refine ContinuousOn.mul (continuousOn_const.mul ?_) ?_
      · exact continuousOn_of_forall_continuousAt fun x hx =>
          Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr (ne_of_gt hx))
      · refine Complex.continuous_ofReal.comp_continuousOn ?_
        unfold kernel
        exact ContinuousOn.div (by fun_prop) (by fun_prop) fun x hx =>
          (sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hx))).ne'
    · rw [(holomorphicOverlap_eq_mul_reading_and_norm_sq t j s hv).2.1,
        ← kernel_center_eq_inv_two_sinh t j hv]
  have hnorm_eq : ∀ v : ℝ, 0 < v →
      ‖holomorphicOverlap t j s v / (v : ℂ)‖ =
        ((tailRadix t j).val : ℝ) ^ (s.re / 2) * (v ^ (s.re - 1) * kernel C a₀ v) := by
    intro v hv
    have hker_pos : 0 < kernel C a₀ v := by
      unfold kernel
      exact div_pos (Real.exp_pos _) (sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hv)))
    rw [(holomorphicOverlap_eq_mul_reading_and_norm_sq t j s hv).2.1,
      ← kernel_center_eq_inv_two_sinh t j hv, norm_div, norm_mul, norm_mul,
      show ((tailRadix t j).val : ℂ) = (((tailRadix t j).val : ℝ) : ℂ) by exact
        (Complex.ofReal_natCast _).symm,
      Complex.norm_cpow_eq_rpow_re_of_pos hC_pos,
      Complex.norm_cpow_eq_rpow_re_of_pos hv,
      Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg hker_pos.le, Real.norm_of_nonneg hv.le]
    have hre_half : (s / 2).re = s.re / 2 := by simp
    have hvp : v ^ s.re / v = v ^ (s.re - 1) := by
      rw [sub_eq_add_neg, Real.rpow_add hv, Real.rpow_neg_one, div_eq_mul_inv]
    rw [hre_half]
    calc (((tailRadix t j).val : ℝ) ^ (s.re / 2) * v ^ s.re * kernel C a₀ v) / v
        = ((tailRadix t j).val : ℝ) ^ (s.re / 2) * ((v ^ s.re / v) * kernel C a₀ v) := by ring
      _ = ((tailRadix t j).val : ℝ) ^ (s.re / 2) * (v ^ (s.re - 1) * kernel C a₀ v) := by
        rw [hvp]
  rw [IntegrableOn, ← integrable_norm_iff (hcont.aestronglyMeasurable measurableSet_Ioi)]
  have hcongr : Integrable (fun v : ℝ => ‖holomorphicOverlap t j s v / (v : ℂ)‖)
      (volume.restrict (Ioi 0)) ↔
      IntegrableOn (fun v : ℝ => ((tailRadix t j).val : ℝ) ^ (s.re / 2) *
        (v ^ (s.re - 1) * kernel C a₀ v)) (Ioi 0) :=
    integrableOn_congr_fun (fun v hv => hnorm_eq v hv) measurableSet_Ioi
  rw [hcongr]
  constructor
  · intro hint
    have hker : IntegrableOn (fun v : ℝ => v ^ (s.re - 1) * kernel C a₀ v) (Ioi 0) := by
      refine IntegrableOn.congr_fun
        (hint.const_mul (((tailRadix t j).val : ℝ) ^ (s.re / 2))⁻¹)
        (fun v _ => ?_) measurableSet_Ioi
      field_simp [hc_pos.ne']
    have hp := (integrableOn_rpow_mul_kernel_iff C ha₀ (s.re - 1)).mp hker
    linarith
  · intro hs1
    have hp : 0 < s.re - 1 := by linarith
    exact ((integrableOn_rpow_mul_kernel_iff C ha₀ (s.re - 1)).mpr hp).const_mul _

private theorem boson_fermion_dyadic_sinh_eq {v : ℝ} (hv : 0 < v) :
    1 / (2 * Real.sinh (v / 2)) - 1 / Real.sinh v =
      (Real.exp (v / 2) + 1)⁻¹ - (Real.exp v + 1)⁻¹ := by
  set u : ℝ := Real.exp (v / 2)
  have hu0 : 0 < u := Real.exp_pos _
  have hu1 : 1 < u := Real.one_lt_exp_iff.mpr (half_pos hv)
  have hu_m1 : u - 1 ≠ 0 := by linarith
  have hu_p1 : u + 1 ≠ 0 := by linarith
  have hu2_p1 : u ^ 2 + 1 ≠ 0 := by nlinarith
  have hexp_v : Real.exp v = u ^ 2 := by
    dsimp only [u]; rw [sq, ← Real.exp_add, add_halves]
  have hsh1 : 2 * Real.sinh (v / 2) = ((u - 1) * (u + 1)) / u := by
    rw [Real.sinh_eq, show Real.exp (-(v / 2)) = u⁻¹ from Real.exp_neg _]
    change 2 * ((u - u⁻¹) / 2) = _
    field_simp [hu0.ne']
    ring
  have hsh2 : Real.sinh v = ((u - 1) * (u + 1) * (u ^ 2 + 1)) / (2 * u ^ 2) := by
    rw [Real.sinh_eq, hexp_v, Real.exp_neg, hexp_v]
    field_simp [hu0.ne']
    ring
  rw [hsh1, hsh2, hexp_v]
  change 1 / (((u - 1) * (u + 1)) / u) -
      1 / (((u - 1) * (u + 1) * (u ^ 2 + 1)) / (2 * u ^ 2)) =
    (u + 1)⁻¹ - (u ^ 2 + 1)⁻¹
  field_simp [hu0.ne', hu_m1, hu_p1, hu2_p1]
  ring

private theorem dyadicOverlapContrast_div_eq_salemFermi (t : ExceptionalTime) (j : ℕ) (s : ℂ)
    {v : ℝ} (hv : 0 < v) :
    dyadicOverlapContrast t j s v / (v : ℂ) =
      ((tailRadix t j).val : ℂ) ^ (s / 2) *
        ((v : ℂ) ^ (s - 1) • _root_.RHTower.salemFermiKernel ((1 / 2 : ℝ) * v) -
          (v : ℂ) ^ (s - 1) • _root_.RHTower.salemFermiKernel v) := by
  have hv2 : 0 < 2 * v := mul_pos two_pos hv
  have hv_ne : (v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hv.ne'
  unfold dyadicOverlapContrast
  rw [(holomorphicOverlap_eq_mul_reading_and_norm_sq t j s hv).2.1,
    (holomorphicOverlap_eq_mul_reading_and_norm_sq t j s hv2).2.1]
  have h2v_cpow : (((2 * v : ℝ) : ℂ)) ^ s = (2 : ℂ) ^ s * (v : ℂ) ^ s := by
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg zero_le_two hv.le, Complex.ofReal_ofNat]
  have h2_pow : (2 : ℂ) ^ (1 - s) * (2 : ℂ) ^ s = 2 := by
    rw [← Complex.cpow_add _ _ two_ne_zero, sub_add_cancel, Complex.cpow_one]
  have h2v_div : 2 * v / 2 = v := mul_div_cancel_left₀ v two_ne_zero
  have hv_div : (v : ℂ) ^ s / (v : ℂ) = (v : ℂ) ^ (s - 1) := by
    rw [sub_eq_add_neg, Complex.cpow_add _ _ hv_ne, Complex.cpow_neg_one, div_eq_mul_inv]
  have hbf : (((1 / (2 * Real.sinh (v / 2)) : ℝ) : ℂ)) -
      2 * (((1 / (2 * Real.sinh v) : ℝ) : ℂ)) =
      _root_.RHTower.salemFermiKernel ((1 / 2 : ℝ) * v) -
        _root_.RHTower.salemFermiKernel v := by
    have htwo : 2 * (((1 / (2 * Real.sinh v) : ℝ) : ℂ)) = (((1 / Real.sinh v : ℝ) : ℂ)) := by
      rw [← Complex.ofReal_ofNat, ← Complex.ofReal_mul]
      congr 1; ring
    rw [htwo, ← Complex.ofReal_sub, boson_fermion_dyadic_sinh_eq hv, Complex.ofReal_sub]
    simp only [_root_.RHTower.salemFermiKernel, Complex.ofReal_inv, Complex.ofReal_add,
      Complex.ofReal_one, one_div, inv_mul_eq_div]
  rw [h2v_cpow, h2v_div]
  calc (((tailRadix t j).val : ℂ) ^ (s / 2) * (v : ℂ) ^ s *
          (((1 / (2 * Real.sinh (v / 2)) : ℝ) : ℂ)) -
        (2 : ℂ) ^ (1 - s) *
          (((tailRadix t j).val : ℂ) ^ (s / 2) * ((2 : ℂ) ^ s * (v : ℂ) ^ s) *
            (((1 / (2 * Real.sinh v) : ℝ) : ℂ)))) / (v : ℂ)
      = ((tailRadix t j).val : ℂ) ^ (s / 2) * ((v : ℂ) ^ s / (v : ℂ)) *
          ((((1 / (2 * Real.sinh (v / 2)) : ℝ) : ℂ)) -
            ((2 : ℂ) ^ (1 - s) * (2 : ℂ) ^ s) * (((1 / (2 * Real.sinh v) : ℝ) : ℂ))) := by
        ring
    _ = ((tailRadix t j).val : ℂ) ^ (s / 2) * (v : ℂ) ^ (s - 1) *
          (_root_.RHTower.salemFermiKernel ((1 / 2 : ℝ) * v) -
            _root_.RHTower.salemFermiKernel v) := by
        rw [hv_div, h2_pow, hbf]
    _ = _ := by simp only [smul_eq_mul]; ring

/-- **Haar integrability of `dyadicOverlapContrast` across the entire right half-plane:**
for every `s` with `0 < Re s` (including `0 < Re s ≤ 1`), `v ↦ dyadicOverlapContrast t j s v / v`
is integrable on `(0, ∞)`. -/
theorem integrableOn_dyadicOverlapContrast_div (t : ExceptionalTime) (j : ℕ)
    {s : ℂ} (hs0 : 0 < s.re) :
    IntegrableOn (fun v : ℝ => dyadicOverlapContrast t j s v / (v : ℂ)) (Ioi 0) := by
  have hf : MellinConvergent _root_.RHTower.salemFermiKernel s :=
    mellinConvergent_of_isBigO_rpow_exp (a := 1) (b := 0) zero_lt_one
      _root_.RHTower.salemFermiKernel_locallyIntegrableOn
      _root_.RHTower.salemFermiKernel_isBigO_exp_neg
      _root_.RHTower.salemFermiKernel_isBigO_one_at_zero hs0
  have hf_half : MellinConvergent
      (fun v : ℝ => _root_.RHTower.salemFermiKernel ((1 / 2 : ℝ) * v)) s :=
    (MellinConvergent.comp_mul_left (by norm_num : (0 : ℝ) < 1 / 2)).mpr hf
  exact IntegrableOn.congr_fun
    ((hf_half.sub hf).const_mul (((tailRadix t j).val : ℂ) ^ (s / 2)))
    (fun v hv => (dyadicOverlapContrast_div_eq_salemFermi t j s hv).symm) measurableSet_Ioi

/-- **Unrenormalized Haar integral of `dyadicOverlapContrast` for `continued`:**
for every `s` with `0 < Re s` and `s ≠ 1`,
`∫_{v > 0} dyadicOverlapContrast(t, j, s, v) / v = C^{s/2} (1 - 2^{1-s}) Γ(s) continued(s)`. -/
theorem integral_dyadicOverlapContrast_div_eq (t : ExceptionalTime) (j : ℕ)
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s ≠ 1) :
    (∫ v : ℝ in Ioi 0, dyadicOverlapContrast t j s v / (v : ℂ)) =
      ((tailRadix t j).val : ℂ) ^ (s / 2) * (1 - (2 : ℂ) ^ (1 - s)) *
        Complex.Gamma s * continued s := by
  have hf : MellinConvergent _root_.RHTower.salemFermiKernel s :=
    mellinConvergent_of_isBigO_rpow_exp (a := 1) (b := 0) zero_lt_one
      _root_.RHTower.salemFermiKernel_locallyIntegrableOn
      _root_.RHTower.salemFermiKernel_isBigO_exp_neg
      _root_.RHTower.salemFermiKernel_isBigO_one_at_zero hs0
  have hf_half : MellinConvergent
      (fun v : ℝ => _root_.RHTower.salemFermiKernel ((1 / 2 : ℝ) * v)) s :=
    (MellinConvergent.comp_mul_left (by norm_num : (0 : ℝ) < 1 / 2)).mpr hf
  have hcongr : (∫ v : ℝ in Ioi 0, dyadicOverlapContrast t j s v / (v : ℂ)) =
      ((tailRadix t j).val : ℂ) ^ (s / 2) *
        (mellin (fun v : ℝ => _root_.RHTower.salemFermiKernel ((1 / 2 : ℝ) * v)) s -
          mellin _root_.RHTower.salemFermiKernel s) := by
    rw [setIntegral_congr_fun measurableSet_Ioi
      (fun v hv => dyadicOverlapContrast_div_eq_salemFermi t j s hv),
      integral_const_mul, integral_sub hf_half hf]
    rfl
  have hscale : mellin (fun v : ℝ => _root_.RHTower.salemFermiKernel ((1 / 2 : ℝ) * v)) s =
      (2 : ℂ) ^ s * mellin _root_.RHTower.salemFermiKernel s := by
    rw [mellin_comp_mul_left _ s (by norm_num : (0 : ℝ) < 1 / 2)]
    have harg : (2 : ℂ).arg ≠ Real.pi := by
      rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
        Complex.arg_ofReal_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      exact Real.pi_pos.ne
    have hhalf : (((1 / 2 : ℝ) : ℂ)) ^ (-s) = (2 : ℂ) ^ s := by
      rw [show (((1 / 2 : ℝ) : ℂ)) = (2 : ℂ)⁻¹ by norm_num,
        Complex.inv_cpow (2 : ℂ) (-s) harg, Complex.cpow_neg, inv_inv]
    rw [hhalf, smul_eq_mul]
  rw [hcongr, hscale, _root_.RHTower.mellin_salemFermiKernel_eq_closedForm hs0 hs1]
  unfold continued
  ring

private theorem one_sub_two_cpow_one_sub_ne_zero {s : ℂ} (hs_re : s.re ≠ 1) :
    1 - (2 : ℂ) ^ (1 - s) ≠ 0 := by
  intro h0
  have heq : (2 : ℂ) ^ (1 - s) = 1 := (sub_eq_zero.mp h0).symm
  have hnorm := congrArg norm heq
  rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
    Complex.norm_cpow_eq_rpow_re_of_pos two_pos, norm_one] at hnorm
  have hexp0 : (1 - s).re = 0 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact (Real.rpow_lt_one_of_one_lt_of_neg one_lt_two hlt).ne hnorm
    · exact (Real.one_lt_rpow one_lt_two hgt).ne' hnorm
  rw [Complex.sub_re, Complex.one_re] at hexp0
  exact hs_re (sub_eq_zero.mp hexp0).symm

/-- On the trace half-plane `1 < Re s`, the unsubtracted `holomorphicOverlap` Haar integral equals
`C^{s/2} Γ(s) continued(s)`. -/
theorem integral_holomorphicOverlap_div_eq (t : ExceptionalTime) (j : ℕ)
    {s : ℂ} (hs1 : 1 < s.re) :
    (∫ v : ℝ in Ioi 0, holomorphicOverlap t j s v / (v : ℂ)) =
      ((tailRadix t j).val : ℂ) ^ (s / 2) * Complex.Gamma s * continued s := by
  have hs0 : 0 < s.re := zero_lt_one.trans hs1
  have hs_ne1 : s ≠ 1 := fun he => hs1.ne' (by rw [he, Complex.one_re])
  set g : ℝ → ℂ := fun u => holomorphicOverlap t j s u / (u : ℂ)
  have hg_int : IntegrableOn g (Ioi 0) :=
    (integrableOn_holomorphicOverlap_div_iff t j s).mpr hs1
  have hg2_int : IntegrableOn (fun v : ℝ => g (2 * v)) (Ioi 0) := by
    refine (integrableOn_Ioi_comp_mul_left_iff g 0 two_pos).mpr ?_
    rwa [mul_zero]
  have h2v_eq : EqOn (fun v : ℝ => holomorphicOverlap t j s (2 * v) / (v : ℂ))
      (fun v : ℝ => (2 : ℂ) * g (2 * v)) (Ioi 0) := by
    intro v hv
    have hv_ne : (v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hv)
    dsimp only [g]
    rw [Complex.ofReal_mul, Complex.ofReal_ofNat]
    field_simp [hv_ne]
  have hint_sub : (∫ v : ℝ in Ioi 0, dyadicOverlapContrast t j s v / (v : ℂ)) =
      (1 - (2 : ℂ) ^ (1 - s)) * ∫ v : ℝ in Ioi 0, g v := by
    have hsplit : EqOn (fun v : ℝ => dyadicOverlapContrast t j s v / (v : ℂ))
        (fun v : ℝ => g v - (2 : ℂ) ^ (1 - s) * ((2 : ℂ) * g (2 * v))) (Ioi 0) := by
      intro v hv
      have h2 : holomorphicOverlap t j s (2 * v) / (v : ℂ) = (2 : ℂ) * g (2 * v) := h2v_eq hv
      dsimp only
      unfold dyadicOverlapContrast
      rw [sub_div, mul_div_assoc, h2]
    rw [setIntegral_congr_fun measurableSet_Ioi hsplit,
      integral_sub hg_int ((hg2_int.const_mul 2).const_mul _),
      integral_const_mul, integral_const_mul,
      integral_comp_mul_left_Ioi g 0 two_pos, mul_zero]
    simp only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_ofNat]
    have h2 : (2 : ℂ) * ((2 : ℂ)⁻¹ * ∫ v : ℝ in Ioi 0, g v) = ∫ v : ℝ in Ioi 0, g v := by
      rw [← mul_assoc, mul_inv_cancel₀ two_ne_zero, one_mul]
    rw [h2]
    ring
  have hclosed := integral_dyadicOverlapContrast_div_eq t j hs0 hs_ne1
  rw [hint_sub] at hclosed
  have hfac_ne : 1 - (2 : ℂ) ^ (1 - s) ≠ 0 := one_sub_two_cpow_one_sub_ne_zero hs1.ne'
  apply mul_left_cancel₀ hfac_ne
  linear_combination hclosed

/-- **Exact zero detection across the critical strip via `dyadicOverlapContrast`:**
for every `s` with `0 < Re s` and `Re s ≠ 1` (in particular across the entire open strip
`0 < Re s < 1`), the Haar integral of `dyadicOverlapContrast t j s v / v` vanishes if and only if
`continued s = 0`. -/
theorem continued_eq_zero_iff_integral_dyadicOverlapContrast_eq_zero
    (t : ExceptionalTime) (j : ℕ) {s : ℂ} (hs0 : 0 < s.re) (hs_re : s.re ≠ 1) :
    (∫ v : ℝ in Ioi 0, dyadicOverlapContrast t j s v / (v : ℂ)) = 0 ↔ continued s = 0 := by
  have hs1 : s ≠ 1 := fun he => hs_re (by rw [he, Complex.one_re])
  rw [integral_dyadicOverlapContrast_div_eq t j hs0 hs1]
  have hC_ne : ((tailRadix t j).val : ℂ) ^ (s / 2) ≠ 0 := by
    have hC0 : ((tailRadix t j).val : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (tailRadix t j).pos.ne'
    rw [Complex.cpow_def_of_ne_zero hC0]
    exact Complex.exp_ne_zero _
  have h2_ne : 1 - (2 : ℂ) ^ (1 - s) ≠ 0 := one_sub_two_cpow_one_sub_ne_zero hs_re
  have hG_ne : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hs0
  have hpre_ne : ((tailRadix t j).val : ℂ) ^ (s / 2) * (1 - (2 : ℂ) ^ (1 - s)) *
      Complex.Gamma s ≠ 0 :=
    mul_ne_zero (mul_ne_zero hC_ne h2_ne) hG_ne
  exact mul_eq_zero_iff_left hpre_ne

/-! ### Part 3: Direct surviving-partition trace exponents and unified conservation criteria -/

/-- Unsubtracted joint surviving Gibbs partition `((2 : ℂ)^z - 1) * survivingPartition b z` on a
spectral band `b`. Unlike `relativePartition`, it retains `continued z` on `hotEdge r`. -/
def jointSurvivingPartition {r : ℕ} (b : SpectralBand r) (z : ℂ) : ℂ :=
  ((2 : ℂ) ^ z - 1) * survivingPartition b z

theorem jointSurvivingPartition_eq_continued_sub {r : ℕ} (b : SpectralBand r) (z : ℂ) :
    jointSurvivingPartition b z = continued z - ((2 : ℂ) ^ z - 1) * relativePartition b z := by
  unfold jointSurvivingPartition survivingPartition continued
  ring

theorem jointSurvivingPartition_hot (r : ℕ) (z : ℂ) :
    jointSurvivingPartition (hotEdge r) z = continued z := by
  rw [jointSurvivingPartition_eq_continued_sub, relativePartition_hot, mul_zero, sub_zero]

/-- Power-`p` control of the unsubtracted joint surviving partition by the fourth-trace deficit
across all positive conserving propagators of missing dimension `r`. -/
def jointSurvivingControlsAt (r : ℕ) (z : ℂ) (p K : ℝ) : Prop :=
  ∀ (P : Projection) (hd : MissingDimension P r) (hc : Conserving (projected P)),
    ‖jointSurvivingPartition (physicalSpectrum P hd hc) z‖ ^ p ≤ K * traceLoss (projected P)

/-- Admissible positive fourth-trace exponents for the unsubtracted joint surviving partition. -/
def jointSurvivingTracePowers (r : ℕ) (z : ℂ) : Set ℝ :=
  {p | 0 < p ∧ ∃ K : ℝ, jointSurvivingControlsAt r z p K}

private theorem relativeReading_hot (f : SpectralResponse) (r : ℕ) :
    relativeReading f (hotEdge r) = 0 := by
  simp [relativeReading, spectralDrop, hotEdge]

/-- **Arbitrarily small fourth-trace violations whenever `continued z ≠ 0`:**
at every `z` with `0 < Re z` and `continued z ≠ 0`, for every missing dimension `r + 1`, exponent
`p > 0`, constant `K : ℝ`, and tolerance `ε > 0`, there exists a positive conserving propagator of
missing dimension `r + 1` with `0 < traceLoss (projected P) < ε` violating
`‖jointSurvivingPartition b z‖^p ≤ K * traceLoss (projected P)`. -/
theorem exists_small_trace_jointSurviving_violation (r : ℕ) {z : ℂ} (hz : 0 < z.re)
    (hcz : continued z ≠ 0) {p : ℝ} (hp : 0 < p) (K : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (P : Projection) (hd : MissingDimension P (r + 1)) (hc : Conserving (projected P)),
      0 < traceLoss (projected P) ∧ traceLoss (projected P) < ε ∧
      K * traceLoss (projected P) <
        ‖jointSurvivingPartition (physicalSpectrum P hd hc) z‖ ^ p := by
  let δ : GibbsExponent := ⟨z.re, hz⟩
  let B₀ : ℝ := ‖continued z‖ +
    ‖(2 : ℂ) ^ z - 1‖ * (‖z‖ / δ.val * relativeHead (powerResponse δ) (r + 1))
  let B : ℝ := B₀ ^ p
  have hB₀_nn : 0 ≤ B₀ := by
    dsimp only [B₀]
    exact add_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _)
      (mul_nonneg (div_nonneg (norm_nonneg _) hz.le)
        ((relativeReading_bounds _ (hotEdge (r + 1))).1.trans
          (relativeReading_bounds (powerResponse δ) (hotEdge (r + 1))).2)))
  have hb_bound (b : SpectralBand (r + 1)) : ‖jointSurvivingPartition b z‖ ^ p ≤ B := by
    refine Real.rpow_le_rpow (norm_nonneg _) ?_ hp.le
    rw [jointSurvivingPartition_eq_continued_sub]
    calc ‖continued z - ((2 : ℂ) ^ z - 1) * relativePartition b z‖
        ≤ ‖continued z‖ + ‖((2 : ℂ) ^ z - 1) * relativePartition b z‖ := norm_sub_le _ _
      _ = ‖continued z‖ + ‖(2 : ℂ) ^ z - 1‖ * ‖relativePartition b z‖ := by rw [norm_mul]
      _ ≤ B₀ := by
          refine add_le_add_right (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)) _
          exact (relativePartition_norm_le b δ le_rfl).trans
            (mul_le_mul_of_nonneg_left (relativeReading_bounds _ b).2
              (div_nonneg (norm_nonneg _) hz.le))
  let A : ℝ := max K ((B + 1) / ε)
  have hnot : ¬ jointSurvivingControlsAt (r + 1) z p A := by
    intro hctrl
    have hcont_jsp : Continuous (fun b : SpectralBand (r + 1) =>
        ‖jointSurvivingPartition b z‖ ^ p) := by
      have hc1 : Continuous (fun b : SpectralBand (r + 1) => jointSurvivingPartition b z) := by
        simp_rw [jointSurvivingPartition_eq_continued_sub]
        exact Continuous.sub continuous_const (continuous_const.mul
          (continuous_relativePartition_spectrum hz (r + 1)))
      exact (Real.continuous_rpow_const hp.le).comp hc1.norm
    let S : Set (SpectralBand (r + 1)) :=
      {b | ‖jointSurvivingPartition b z‖ ^ p ≤ A * relativeReading quadraticResponse b}
    have hS_closed : IsClosed S :=
      isClosed_le hcont_jsp (continuous_const.mul (continuous_relativeReading _ (r + 1)))
    have hS_sub : physicalSpectra (r + 1) ⊆ S := by
      rintro _ ⟨P, hd, hc, rfl⟩
      change _ ≤ A * relativeReading quadraticResponse _
      rw [quadratic_physicalReading]
      exact hctrl P hd hc
    have hhot_cl : hotEdge (r + 1) ∈ closure (physicalSpectra (r + 1)) :=
      closure_mono (laneSpectra_subset_physicalSpectra (r + 1)) (physical_spectral_edges r).1
    have hhot_S : hotEdge (r + 1) ∈ S := closure_minimal hS_sub hS_closed hhot_cl
    change ‖jointSurvivingPartition (hotEdge (r + 1)) z‖ ^ p ≤
      A * relativeReading quadraticResponse (hotEdge (r + 1)) at hhot_S
    rw [jointSurvivingPartition_hot, relativeReading_hot, mul_zero] at hhot_S
    exact (Real.rpow_pos_of_pos (norm_pos_iff.mpr hcz) p).not_ge hhot_S
  unfold jointSurvivingControlsAt at hnot
  push Not at hnot
  obtain ⟨P, hd, hc, hw⟩ := hnot
  let b := physicalSpectrum P hd hc
  have hD : 0 < traceLoss (projected P) := by
    have h := (physical_reading_interior quadraticResponse P (Nat.succ_pos r) hd hc).1
    rwa [quadratic_physicalReading] at h
  refine ⟨P, hd, hc, hD, ?_, (mul_le_mul_of_nonneg_right (le_max_left _ _) hD.le).trans_lt hw⟩
  by_contra! hbig
  have hB_nn : 0 ≤ B := Real.rpow_nonneg hB₀_nn p
  have hA_nn : 0 ≤ A := (div_nonneg (by linarith : 0 ≤ B + 1) hε.le).trans (le_max_right _ _)
  have hlt := hw.trans_le (hb_bound b)
  have hle := (mul_le_mul_of_nonneg_right (le_max_right K ((B + 1) / ε)) hε.le).trans
    (mul_le_mul_of_nonneg_left hbig hA_nn)
  rw [div_mul_cancel₀ _ hε.ne'] at hle
  linarith

private theorem two_cpow_sub_one_ne_zero {z : ℂ} (hz : 0 < z.re) :
    (2 : ℂ) ^ z - 1 ≠ 0 := by
  intro h0
  obtain ⟨k, hk⟩ := (ComplementaryHalves.factor_zero_iff z).mp h0
  exact hz.ne' ((congrArg Complex.re hk).trans (ComplementaryHalves.frequency_re k))

/-- At any zero of `continued` in `Re z > 0`, `jointSurvivingTracePowers (r + 1) z` coincides with
the ray `[max(1, 2 / Re z), ∞)`. -/
theorem jointSurvivingTracePowers_eq_of_continued_eq_zero (r : ℕ) {z : ℂ} (hz : 0 < z.re)
    (hcz : continued z = 0) :
    jointSurvivingTracePowers (r + 1) z = Ici (max 1 (2 / z.re)) := by
  rw [← admissibleTracePowers_eq r hz]
  have hf_pos : 0 < ‖(2 : ℂ) ^ z - 1‖ := norm_pos_iff.mpr (two_cpow_sub_one_ne_zero hz)
  ext p
  simp only [jointSurvivingTracePowers, admissibleTracePowers, mem_setOf_eq]
  refine and_congr_right fun hp => ?_
  have hfp_pos : 0 < ‖(2 : ℂ) ^ z - 1‖ ^ p := Real.rpow_pos_of_pos hf_pos p
  have hnorm_eq : ∀ b : SpectralBand (r + 1),
      ‖jointSurvivingPartition b z‖ ^ p =
        ‖(2 : ℂ) ^ z - 1‖ ^ p * ‖relativePartition b z‖ ^ p := by
    intro b
    rw [jointSurvivingPartition_eq_continued_sub, hcz, zero_sub, norm_neg, norm_mul,
      Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
  constructor
  · rintro ⟨K, hK⟩
    refine ⟨K / (‖(2 : ℂ) ^ z - 1‖ ^ p), fun P hd hc => ?_⟩
    rw [div_mul_eq_mul_div, le_div_iff₀' hfp_pos, ← hnorm_eq]
    exact hK P hd hc
  · rintro ⟨K, hK⟩
    refine ⟨‖(2 : ℂ) ^ z - 1‖ ^ p * K, fun P hd hc => ?_⟩
    rw [hnorm_eq, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hK P hd hc) hfp_pos.le

/-- **Zero-detection dichotomy for `jointSurvivingTracePowers`:** on `Re z > 0`, at least one
positive surviving-partition trace power exists if and only if `continued z = 0`. -/
theorem nonempty_jointSurvivingTracePowers_iff_continued_eq_zero (r : ℕ) {z : ℂ} (hz : 0 < z.re) :
    (jointSurvivingTracePowers (r + 1) z).Nonempty ↔ continued z = 0 := by
  constructor
  · rintro ⟨p, hp, K, hK⟩
    by_contra hcz
    obtain ⟨P, hd, hc, _, _, hviol⟩ :=
      exists_small_trace_jointSurviving_violation r hz hcz hp K zero_lt_one
    exact (hK P hd hc).not_gt hviol
  · intro hcz
    rw [jointSurvivingTracePowers_eq_of_continued_eq_zero r hz hcz]
    exact nonempty_Ici

/-- **Quartic surviving-partition exponent criterion:** on `Re z > 0`, `4` belongs to
`jointSurvivingTracePowers (r + 1) z` if and only if `continued z = 0` and `1 / 2 ≤ Re z`. -/
theorem mem_jointSurvivingTracePowers_four_iff (r : ℕ) {z : ℂ} (hz : 0 < z.re) :
    (4 : ℝ) ∈ jointSurvivingTracePowers (r + 1) z ↔ continued z = 0 ∧ 1 / 2 ≤ z.re := by
  constructor
  · intro h4
    have hcz : continued z = 0 :=
      (nonempty_jointSurvivingTracePowers_iff_continued_eq_zero r hz).mp ⟨4, h4⟩
    rw [jointSurvivingTracePowers_eq_of_continued_eq_zero r hz hcz, mem_Ici, max_le_iff] at h4
    have hdiv := (div_le_iff₀ hz).mp h4.2
    refine ⟨hcz, by linarith⟩
  · rintro ⟨hcz, hre⟩
    rw [jointSurvivingTracePowers_eq_of_continued_eq_zero r hz hcz, mem_Ici, max_le_iff]
    refine ⟨by norm_num, (div_le_iff₀ hz).mpr (by linarith)⟩

/-- **Simultaneous characterization of partition vanishing and isometric conservation:**
on `Re z > 0`, `4` is the least element of `jointSurvivingTracePowers (r + 1) z` if and only if
`continued z = 0` and `split z` is an isometry (equivalently `continued z = 0` and the diagonal
self-overlap `overlap t j a z z` has a finite nonzero high-temperature limit). -/
theorem isLeast_jointSurvivingTracePowers_four_iff (r : ℕ) (t : ExceptionalTime) (j : ℕ) (a : ℝ)
    {z : ℂ} (hz : 0 < z.re) :
    (IsLeast (jointSurvivingTracePowers (r + 1) z) 4 ↔
      continued z = 0 ∧ ∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split z f x) ∧
    (IsLeast (jointSurvivingTracePowers (r + 1) z) 4 ↔
      continued z = 0 ∧
        ∃ L : ℂ, L ≠ 0 ∧ Tendsto (ComplementaryHalves.overlap t j a z z) (𝓝[>] 0) (𝓝 L)) := by
  have h1 : IsLeast (jointSurvivingTracePowers (r + 1) z) 4 ↔
      continued z = 0 ∧ ∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split z f x := by
    constructor
    · intro hleast
      have hcz : continued z = 0 :=
        (nonempty_jointSurvivingTracePowers_iff_continued_eq_zero r hz).mp ⟨4, hleast.1⟩
      rw [jointSurvivingTracePowers_eq_of_continued_eq_zero r hz hcz,
        ← admissibleTracePowers_eq r hz, least_trace_power_four_iff_split_isometric r hz] at hleast
      exact ⟨hcz, hleast⟩
    · rintro ⟨hcz, hiso⟩
      rw [jointSurvivingTracePowers_eq_of_continued_eq_zero r hz hcz,
        ← admissibleTracePowers_eq r hz]
      exact (least_trace_power_four_iff_split_isometric r hz).mpr hiso
  refine ⟨h1, h1.trans (and_congr_right fun _ => (thermal_iff_isometry t j a z).symm)⟩

/-- **Unconditional surviving-exponent conservation through Bohman height `169 / 2 = 84.5`:**
every open-strip zero of `continued` with `|Im s| ≤ 169 / 2` unconditionally has least surviving
trace power `4` at every positive missing rank `r + 1`. -/
theorem joint_partition_zero_least_surviving_power_four_below_eightyFour_and_half
    (r : ℕ) {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) (him : |s.im| ≤ 169 / 2)
    (hcs : continued s = 0) :
    IsLeast (jointSurvivingTracePowers (r + 1) s) 4 := by
  rw [jointSurvivingTracePowers_eq_of_continued_eq_zero r hs0 hcs,
    ← admissibleTracePowers_eq r hs0, least_trace_power_four_iff_split_isometric r hs0,
    split_isometric_iff]
  have hζ : riemannZeta s = 0 := (ComplementaryHalves.positive_zero_iff ⟨s, hs0⟩).mp hcs
  have hs_ne1 : s ≠ 1 := fun he => hs1.ne (by rw [he, Complex.one_re])
  have hxi : _root_.RHTower.xi s = 0 := (_root_.RHTower.xi_eq_zero_iff hs0 hs_ne1).mpr hζ
  by_contra hne
  have hgt := VerifiedHeightRungs.lt_abs_im_of_rhVerifiedThrough
    VerifiedHeightRungs.HadamardBudget.rhVerifiedThrough_oneHundredSixtyNine_halves
    hxi hs0 hs1 hne
  linarith

/-- **Unified overlap-divisor and surviving-trace-exponent conservation criteria:**
1. `RiemannHypothesis` is unconditionally equivalent to every open-strip zero of the unrenormalized
   dyadic overlap integral having least surviving-partition trace power `4`;
2. Above Bohman height `169 / 2 = 84.5`, functional reflection reduces `RiemannHypothesis` (even at
   missing rank `1`) to `4 ∈ jointSurvivingTracePowers 1 s` at every left-strip point
   `3001 / 24000 ≤ Re s < 1 / 2`, `169 / 2 < |Im s|` where the dyadic overlap integral vanishes. -/
theorem rh_iff_surviving_exponent_four_at_dyadicOverlap_zeros_above_eightyFour_and_half
    (t : ExceptionalTime) (j : ℕ) (r : ℕ) :
    (RiemannHypothesis ↔
      ∀ s : ℂ, 0 < s.re → s.re < 1 →
        (∫ v : ℝ in Ioi 0, dyadicOverlapContrast t j s v / (v : ℂ)) = 0 →
        IsLeast (jointSurvivingTracePowers (r + 1) s) 4) ∧
    (RiemannHypothesis ↔
      ∀ s : ℂ, 3001 / 24000 ≤ s.re → s.re < 1 / 2 → 169 / 2 < |s.im| →
        (∫ v : ℝ in Ioi 0, dyadicOverlapContrast t j s v / (v : ℂ)) = 0 →
        (4 : ℝ) ∈ jointSurvivingTracePowers 1 s) := by
  refine ⟨?_, ?_⟩
  · rw [rh_iff_thermal_at_joint_zeros t j 0]
    constructor
    · intro hRH s hs0 hs1 hint0
      have hcs : continued s = 0 :=
        (continued_eq_zero_iff_integral_dyadicOverlapContrast_eq_zero t j hs0 hs1.ne).mp hint0
      exact ((isLeast_jointSurvivingTracePowers_four_iff r t j 0 hs0).2).mpr
        ⟨hcs, hRH ⟨s, hs0, hs1⟩ hcs⟩
    · intro hall ⟨s, hs0, hs1⟩ hcs
      have hint0 : (∫ v : ℝ in Ioi 0, dyadicOverlapContrast t j s v / (v : ℂ)) = 0 :=
        (continued_eq_zero_iff_integral_dyadicOverlapContrast_eq_zero t j hs0 hs1.ne).mpr hcs
      exact (((isLeast_jointSurvivingTracePowers_four_iff r t j 0 hs0).2).mp
        (hall s hs0 hs1 hint0)).2
  · rw [(rh_iff_unified_residual_elimination_above_eightyFour_and_half t j 0).1]
    constructor
    · intro hnoblow s hlo hhi him hint0
      have hs0 : 0 < s.re := by linarith
      have hs1 : s.re < 1 := by linarith
      have hcs : continued s = 0 :=
        (continued_eq_zero_iff_integral_dyadicOverlapContrast_eq_zero t j hs0 hs1.ne).mp hint0
      obtain ⟨B, hfreq⟩ := hnoblow s hlo hhi him hcs
      have htop := tendsto_norm_self_overlap_atTop_of_re_lt_half t j 0 hhi
      have hev : ∀ᶠ v : ℝ in 𝓝[>] 0, B + 1 ≤
          ‖ComplementaryHalves.overlap t j 0 s s v‖ :=
        htop.eventually (tendsto_atTop.mp tendsto_id (B + 1))
      obtain ⟨v, hv_le, hv_ge⟩ := (hfreq.and_eventually hev).exists
      linarith
    · intro hmem4 s hlo hhi him hcs
      have hs0 : 0 < s.re := by linarith
      have hs1 : s.re < 1 := by linarith
      have hint0 : (∫ v : ℝ in Ioi 0, dyadicOverlapContrast t j s v / (v : ℂ)) = 0 :=
        (continued_eq_zero_iff_integral_dyadicOverlapContrast_eq_zero t j hs0 hs1.ne).mpr hcs
      have h4 := hmem4 s hlo hhi him hint0
      have hge := ((mem_jointSurvivingTracePowers_four_iff 0 hs0).mp h4).2
      linarith

#print axioms overlap_vertical_shift_eq
#print axioms norm_self_overlap_vertical_invariant
#print axioms exists_nonvanishing_real_with_identical_self_overlap
#print axioms sqrt_kernel_le_cutoffHeat_and_le
#print axioms integrableOn_norm_sq_reading_haar_iff
#print axioms split_isometric_iff_reading_haar_frontier
#print axioms holomorphicOverlap_eq_mul_reading_and_norm_sq
#print axioms integrableOn_holomorphicOverlap_div_iff
#print axioms integrableOn_dyadicOverlapContrast_div
#print axioms integral_dyadicOverlapContrast_div_eq
#print axioms integral_holomorphicOverlap_div_eq
#print axioms continued_eq_zero_iff_integral_dyadicOverlapContrast_eq_zero
#print axioms exists_small_trace_jointSurviving_violation
#print axioms jointSurvivingTracePowers_eq_of_continued_eq_zero
#print axioms nonempty_jointSurvivingTracePowers_iff_continued_eq_zero
#print axioms mem_jointSurvivingTracePowers_four_iff
#print axioms isLeast_jointSurvivingTracePowers_four_iff
#print axioms joint_partition_zero_least_surviving_power_four_below_eightyFour_and_half
#print axioms rh_iff_surviving_exponent_four_at_dyadicOverlap_zeros_above_eightyFour_and_half

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas
