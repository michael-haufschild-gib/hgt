import GaloisForLFunctions.RHTower.CircleHankelSeamEnergy
import GaloisForLFunctions.HTGeometry.SquareIntegrableKernelOperator

/-!
# The Szegő kernel form of the Hardy commutator on the circle

Write `e(θ)` for the unit character of `ℝ/ℤ` and `S(θ) = (1 - e(θ))⁻¹` for the Szegő factor, so
that formally `(P f)(z) = ∫ S(z - w) f(w) dw`.  For a bounded symbol `a` of finite half-Sobolev
energy the commutator kernel

`c_a(z, w) = (a(w) - a(z)) S(z - w)`

is square integrable on the torus, with the Douglas identity

`∬ |c_a|² = ∑_n |n| |â(n)|²`:

after the substitution `w = z - θ`, Parseval for the translate difference gives
`∫ |a(z - θ) - a(z)|² dz = ∑_n |â(n)|² |e(-nθ) - 1|²`, and `(e(-nθ) - 1) S(θ)` is a geometric
trigonometric polynomial with `|n|` unimodular terms.
-/

noncomputable section

open Complex MeasureTheory Set Filter ContinuousLinearMap
open scoped ENNReal Real

namespace RHTower

/-! ## Characters and the Szegő factor -/

theorem norm_fourier_apply_eq_one (n : ℤ) (z : AddCircle (1 : ℝ)) : ‖fourier n z‖ = 1 := by
  rw [fourier_apply]
  exact Circle.norm_coe _

theorem fourier_apply_add (n : ℤ) (x y : AddCircle (1 : ℝ)) :
    fourier n (x + y) = fourier n x * fourier n y := by
  rw [fourier_apply, fourier_apply, fourier_apply, smul_add, AddCircle.toCircle_add,
    Circle.coe_mul]

/-- The Szegő factor `S(θ) = (1 - e(θ))⁻¹`. -/
def szegoFactor (θ : AddCircle (1 : ℝ)) : ℂ := (1 - fourier 1 θ)⁻¹

theorem measurable_szegoFactor : Measurable szegoFactor :=
  ((continuous_const.sub (fourier 1).continuous).measurable).inv

theorem fourier_one_ne_one {θ : AddCircle (1 : ℝ)} (hθ : θ ≠ 0) : fourier 1 θ ≠ 1 := by
  intro h
  apply hθ
  rw [fourier_one] at h
  have h' : AddCircle.toCircle θ = AddCircle.toCircle (0 : AddCircle (1 : ℝ)) := by
    rw [AddCircle.toCircle_zero]; exact Circle.ext h
  exact AddCircle.injective_toCircle one_ne_zero h'

theorem haarAddCircle_singleton (x : AddCircle (1 : ℝ)) :
    AddCircle.haarAddCircle ({x} : Set (AddCircle (1 : ℝ))) = 0 := by
  have hvol : (AddCircle.haarAddCircle : Measure (AddCircle (1 : ℝ))) = volume := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]; simp
  rw [hvol, ← Metric.closedBall_zero, AddCircle.volume_closedBall]
  simp

theorem haarAddCircle_ae_ne_zero : ∀ᵐ θ ∂(AddCircle.haarAddCircle : Measure (AddCircle (1 : ℝ))), θ ≠ 0 :=
  measure_eq_zero_iff_ae_notMem.1 (haarAddCircle_singleton 0)

/-- Negative geometric polynomial `∑_{j < k} e(-(j+1)θ)`. -/
def szegoNegGeom (k : ℕ) (θ : AddCircle (1 : ℝ)) : ℂ :=
  ∑ j ∈ Finset.range k, fourier (-((j : ℤ) + 1)) θ

/-- Positive geometric polynomial `∑_{j < k} e(jθ)`. -/
def szegoPosGeom (k : ℕ) (θ : AddCircle (1 : ℝ)) : ℂ :=
  ∑ j ∈ Finset.range k, fourier (j : ℤ) θ

theorem fourier_negNat_sub_one (k : ℕ) (θ : AddCircle (1 : ℝ)) :
    fourier (-(k : ℤ)) θ - 1 = (1 - fourier 1 θ) * szegoNegGeom k θ := by
  induction k with
  | zero => simp [szegoNegGeom]
  | succ k ih =>
    rw [szegoNegGeom, Finset.sum_range_succ, ← szegoNegGeom, mul_add, ← ih]
    have h : fourier (-(k : ℤ)) θ = fourier 1 θ * fourier (-((k : ℤ) + 1)) θ := by
      rw [← fourier_add]; ring_nf
    push_cast
    rw [h]
    ring

theorem fourier_nat_sub_one (k : ℕ) (θ : AddCircle (1 : ℝ)) :
    fourier (k : ℤ) θ - 1 = -((1 - fourier 1 θ) * szegoPosGeom k θ) := by
  induction k with
  | zero => simp [szegoPosGeom]
  | succ k ih =>
    rw [szegoPosGeom, Finset.sum_range_succ, ← szegoPosGeom, mul_add, neg_add, ← ih]
    have h : fourier ((k : ℤ) + 1) θ = fourier (k : ℤ) θ * fourier 1 θ := by
      rw [← fourier_add]
    push_cast
    rw [h]
    ring

/-- Geometric quotient `(e(-nθ) - 1) / (1 - e(θ))` as a trigonometric polynomial. -/
def szegoGeom (n : ℤ) (θ : AddCircle (1 : ℝ)) : ℂ :=
  if 0 ≤ n then szegoNegGeom n.toNat θ else -szegoPosGeom (-n).toNat θ

theorem fourier_neg_sub_one_eq (n : ℤ) (θ : AddCircle (1 : ℝ)) :
    fourier (-n) θ - 1 = (1 - fourier 1 θ) * szegoGeom n θ := by
  rcases le_or_gt 0 n with hn | hn
  · rw [szegoGeom, if_pos hn, ← fourier_negNat_sub_one, Int.toNat_of_nonneg hn]
  · rw [szegoGeom, if_neg (not_le.2 hn), mul_neg, ← fourier_nat_sub_one,
      Int.toNat_of_nonneg (by omega : 0 ≤ -n)]

theorem szegoGeom_eq (n : ℤ) {θ : AddCircle (1 : ℝ)} (hθ : θ ≠ 0) :
    (fourier (-n) θ - 1) * szegoFactor θ = szegoGeom n θ := by
  have hne : (1 : ℂ) - fourier 1 θ ≠ 0 := sub_ne_zero.2 (fourier_one_ne_one hθ).symm
  rw [fourier_neg_sub_one_eq, szegoFactor, mul_comm (1 - _), mul_assoc, mul_inv_cancel₀ hne,
    mul_one]

theorem continuous_szegoGeom (n : ℤ) : Continuous (szegoGeom n) := by
  unfold szegoGeom szegoNegGeom szegoPosGeom
  split_ifs
  · exact continuous_finsetSum _ fun j _ => (fourier _).continuous
  · exact (continuous_finsetSum _ fun j _ => (fourier _).continuous).neg

/-- Square mean of a sum of distinct characters: `∫ |∑_{j ∈ s} e(c j)|² = |s|`. -/
theorem lintegral_enorm_sum_fourier_sq {s : Finset ℕ} (c : ℕ → ℤ) (hc : Function.Injective c) :
    ∫⁻ θ : AddCircle (1 : ℝ), ‖∑ j ∈ s, fourier (c j) θ‖ₑ ^ 2 ∂AddCircle.haarAddCircle =
      s.card := by
  let g : C(AddCircle (1 : ℝ), ℂ) := ∑ j ∈ s, fourier (c j)
  have hg : ∀ θ, g θ = ∑ j ∈ s, fourier (c j) θ := fun θ => by simp [g]
  have hcont : Continuous fun θ => ‖g θ‖ ^ 2 := by fun_prop
  have hint : Integrable (fun θ => ‖g θ‖ ^ 2) AddCircle.haarAddCircle :=
    integrableOn_univ.1 (hcont.continuousOn.integrableOn_compact isCompact_univ)
  have hlin : ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ g =
      ∑ j ∈ s, (fourierLp (T := (1 : ℝ)) 2 (c j) : CCMCircleL2) := by
    simp [g, map_sum]
  have hinner : inner ℂ (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ g)
      (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ g) = s.card := by
    rw [hlin]
    have h := ((orthonormal_fourier (T := (1 : ℝ))).comp c hc).inner_sum (fun _ => 1)
      (fun _ => 1) s
    simp only [one_smul, Function.comp_apply, map_one, mul_one, Finset.sum_const,
      nsmul_eq_mul, mul_one] at h
    exact h
  rw [ContinuousMap.inner_toLp] at hinner
  have hreal : ∫ θ, ‖g θ‖ ^ 2 ∂AddCircle.haarAddCircle = s.card := by
    have h2 : (fun θ => g θ * starRingEnd ℂ (g θ)) = fun θ => ((‖g θ‖ ^ 2 : ℝ) : ℂ) := by
      funext θ; rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [h2, integral_complex_ofReal] at hinner
    exact_mod_cast hinner
  calc ∫⁻ θ : AddCircle (1 : ℝ), ‖∑ j ∈ s, fourier (c j) θ‖ₑ ^ 2 ∂AddCircle.haarAddCircle
      = ∫⁻ θ, ENNReal.ofReal (‖g θ‖ ^ 2) ∂AddCircle.haarAddCircle := by
        refine lintegral_congr fun θ => ?_
        rw [hg, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    _ = ENNReal.ofReal (∫ θ, ‖g θ‖ ^ 2 ∂AddCircle.haarAddCircle) :=
        (ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun _ => by positivity)).symm
    _ = s.card := by rw [hreal, ENNReal.ofReal_natCast]

/-- `∫ |(e(-nθ) - 1) S(θ)|² dθ = |n|`. -/
theorem lintegral_enorm_szegoGeom_sq (n : ℤ) :
    ∫⁻ θ, ‖szegoGeom n θ‖ₑ ^ 2 ∂AddCircle.haarAddCircle = (n.natAbs : ℝ≥0∞) := by
  rcases le_or_gt 0 n with hn | hn
  · have h := lintegral_enorm_sum_fourier_sq (s := Finset.range n.toNat)
      (fun j : ℕ => -((j : ℤ) + 1)) (fun a b hab => by simpa using hab)
    simp only [Finset.card_range] at h
    rw [show n.natAbs = n.toNat by omega, ← h]
    refine lintegral_congr fun θ => ?_
    rw [szegoGeom, if_pos hn, szegoNegGeom]
  · have h := lintegral_enorm_sum_fourier_sq (s := Finset.range (-n).toNat)
      (fun j : ℕ => (j : ℤ)) (fun a b hab => by simpa using hab)
    simp only [Finset.card_range] at h
    rw [show n.natAbs = (-n).toNat by omega, ← h]
    refine lintegral_congr fun θ => ?_
    rw [szegoGeom, if_neg (not_le.2 hn), enorm_neg, szegoPosGeom]

/-! ## Translates and the Douglas energy -/

/-- Fourier coefficients of a translate: `(a(· - θ))^(n) = e(-nθ) â(n)`. -/
theorem fourierCoeff_translate (a : AddCircle (1 : ℝ) → ℂ) (θ : AddCircle (1 : ℝ)) (n : ℤ) :
    fourierCoeff (fun z => a (z - θ)) n = fourier (-n) θ * fourierCoeff a n := by
  rw [fourierCoeff, fourierCoeff]
  have h := integral_add_right_eq_self (μ := AddCircle.haarAddCircle)
    (fun z => fourier (-n) z • a (z - θ)) θ
  simp only [add_sub_cancel_right] at h
  rw [← h]
  simp_rw [fourier_apply_add, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1
  funext y
  ring

theorem enorm_sq_eq_ofReal (c : ℂ) : ‖c‖ₑ ^ 2 = ENNReal.ofReal (‖c‖ ^ 2) := by
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]

/-- Parseval for a translate difference:
`∫ |a(z - θ) - a(z)|² dz = ∑_n |e(-nθ) - 1|² |â(n)|²`. -/
theorem lintegral_enorm_translate_sub_sq (a : CCMCircleBoundedSymbol) (θ : AddCircle (1 : ℝ)) :
    ∫⁻ z, ‖a.toFun (z - θ) - a.toFun z‖ₑ ^ 2 ∂AddCircle.haarAddCircle =
      ∑' n : ℤ, ‖fourier (-n) θ - 1‖ₑ ^ 2 * ‖fourierCoeff a.toFun n‖ₑ ^ 2 := by
  let g : AddCircle (1 : ℝ) → ℂ := fun z => a.toFun (z - θ) - a.toFun z
  have hmeas_t : Measurable fun z => a.toFun (z - θ) := a.measurable.comp (measurable_sub_const θ)
  have hg : Measurable g := hmeas_t.sub a.measurable
  have hgb : ∀ z, ‖g z‖ ≤ 2 * a.bound := fun z =>
    (norm_sub_le _ _).trans (by linarith [a.norm_le (z - θ), a.norm_le z])
  have hmem : MemLp g 2 AddCircle.haarAddCircle :=
    MemLp.of_bound hg.aestronglyMeasurable (2 * a.bound) (Eventually.of_forall hgb)
  have hP := hasSum_sq_fourierCoeff hmem.toLp
  have hcoeff : ∀ n, fourierCoeff ((hmem.toLp : CCMCircleL2) : AddCircle (1 : ℝ) → ℂ) n =
      (fourier (-n) θ - 1) * fourierCoeff a.toFun n := by
    intro n
    rw [fourierCoeff_congr_ae (MemLp.coeFn_toLp hmem)]
    have hbd : ∀ (f : AddCircle (1 : ℝ) → ℂ), Measurable f → (∀ z, ‖f z‖ ≤ a.bound) →
        Integrable (fun z => fourier (-n) z • f z) AddCircle.haarAddCircle := by
      intro f hf hfb
      refine Integrable.of_bound (((fourier (-n)).continuous.measurable).smul hf).aestronglyMeasurable
        a.bound (Eventually.of_forall fun z => ?_)
      rw [norm_smul, norm_fourier_apply_eq_one, one_mul]
      exact hfb z
    have h1 := hbd _ hmeas_t fun z => a.norm_le _
    have h2 := hbd _ a.measurable a.norm_le
    have hsplit : fourierCoeff g n = fourierCoeff (fun z => a.toFun (z - θ)) n -
        fourierCoeff a.toFun n := by
      rw [fourierCoeff, fourierCoeff, fourierCoeff, ← integral_sub h1 h2]
      congr 1
      funext z
      simp only [g, smul_sub]
    rw [hsplit, fourierCoeff_translate]
    ring
  have hint : Integrable (fun z => ‖g z‖ ^ 2) AddCircle.haarAddCircle :=
    Integrable.of_bound (hg.norm.pow_const 2).aestronglyMeasurable ((2 * a.bound) ^ 2)
      (Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hgb z) 2)
  have hreal : ∫ t, ‖((hmem.toLp : CCMCircleL2) : AddCircle (1 : ℝ) → ℂ) t‖ ^ 2
      ∂AddCircle.haarAddCircle = ∫ t, ‖g t‖ ^ 2 ∂AddCircle.haarAddCircle :=
    integral_congr_ae (by filter_upwards [MemLp.coeFn_toLp hmem] with t ht; rw [ht])
  calc ∫⁻ z, ‖a.toFun (z - θ) - a.toFun z‖ₑ ^ 2 ∂AddCircle.haarAddCircle
      = ENNReal.ofReal (∫ t, ‖g t‖ ^ 2 ∂AddCircle.haarAddCircle) := by
        rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun _ => by positivity)]
        exact lintegral_congr fun z => enorm_sq_eq_ofReal _
    _ = ∑' n : ℤ, ENNReal.ofReal (‖fourierCoeff
          ((hmem.toLp : CCMCircleL2) : AddCircle (1 : ℝ) → ℂ) n‖ ^ 2) := by
        rw [← hreal, ← hP.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity)
          hP.summable]
    _ = _ := by
        refine tsum_congr fun n => ?_
        rw [hcoeff, ← enorm_sq_eq_ofReal, enorm_mul, mul_pow]

/-- Commutator kernel `c_a(z, w) = (a(w) - a(z)) S(z - w)`. -/
def szegoCommutatorKernel (a : AddCircle (1 : ℝ) → ℂ) (z w : AddCircle (1 : ℝ)) : ℂ :=
  (a w - a z) * szegoFactor (z - w)

theorem measurable_szegoCommutatorKernel {a : AddCircle (1 : ℝ) → ℂ} (ha : Measurable a) :
    Measurable (Function.uncurry (szegoCommutatorKernel a)) :=
  ((ha.comp measurable_snd).sub (ha.comp measurable_fst)).mul
    (measurable_szegoFactor.comp (measurable_fst.sub measurable_snd))

/-- **Douglas identity.**  `∬ |(a(w) - a(z)) S(z - w)|² = ∑_n |n| |â(n)|²`. -/
theorem lintegral_szegoCommutatorKernel (a : CCMCircleBoundedSymbol) :
    ∫⁻ z, ∫⁻ w, ‖szegoCommutatorKernel a.toFun z w‖ₑ ^ 2 ∂AddCircle.haarAddCircle
        ∂AddCircle.haarAddCircle =
      ∑' n : ℤ, (n.natAbs : ℝ≥0∞) * ‖fourierCoeff a.toFun n‖ₑ ^ 2 := by
  have hmeasF : Measurable fun p : AddCircle (1 : ℝ) × AddCircle (1 : ℝ) =>
      ‖a.toFun (p.1 - p.2) - a.toFun p.1‖ₑ ^ 2 * ‖szegoFactor p.2‖ₑ ^ 2 :=
    (((a.measurable.comp (measurable_fst.sub measurable_snd)).sub
      (a.measurable.comp measurable_fst)).enorm.pow_const 2).mul
      ((measurable_szegoFactor.comp measurable_snd).enorm.pow_const 2)
  have h1 : ∀ z, ∫⁻ w, ‖szegoCommutatorKernel a.toFun z w‖ₑ ^ 2 ∂AddCircle.haarAddCircle =
      ∫⁻ θ, ‖a.toFun (z - θ) - a.toFun z‖ₑ ^ 2 * ‖szegoFactor θ‖ₑ ^ 2
        ∂AddCircle.haarAddCircle := by
    intro z
    rw [← lintegral_sub_left_eq_self (fun w => ‖szegoCommutatorKernel a.toFun z w‖ₑ ^ 2) z]
    refine lintegral_congr fun θ => ?_
    rw [szegoCommutatorKernel, sub_sub_cancel, enorm_mul, mul_pow]
  simp_rw [h1]
  rw [lintegral_lintegral_swap (f := fun z θ =>
    ‖a.toFun (z - θ) - a.toFun z‖ₑ ^ 2 * ‖szegoFactor θ‖ₑ ^ 2) hmeasF.aemeasurable]
  have h3 : ∀ θ, ∫⁻ z, ‖a.toFun (z - θ) - a.toFun z‖ₑ ^ 2 * ‖szegoFactor θ‖ₑ ^ 2
      ∂AddCircle.haarAddCircle =
      ∑' n : ℤ, ‖fourier (-n) θ - 1‖ₑ ^ 2 * ‖fourierCoeff a.toFun n‖ₑ ^ 2 *
        ‖szegoFactor θ‖ₑ ^ 2 := by
    intro θ
    have hm : Measurable fun z => ‖a.toFun (z - θ) - a.toFun z‖ₑ ^ 2 :=
      ((a.measurable.comp (measurable_sub_const θ)).sub a.measurable).enorm.pow_const 2
    rw [lintegral_mul_const _ hm, lintegral_enorm_translate_sub_sq, ENNReal.tsum_mul_right]
  simp_rw [h3]
  have hmn : ∀ n : ℤ, AEMeasurable (fun θ => ‖fourier (-n) θ - 1‖ₑ ^ 2 *
      ‖fourierCoeff a.toFun n‖ₑ ^ 2 * ‖szegoFactor θ‖ₑ ^ 2) AddCircle.haarAddCircle := by
    intro n
    have hm : Measurable fun θ => ‖fourier (-n) θ - 1‖ₑ ^ 2 *
        ‖fourierCoeff a.toFun n‖ₑ ^ 2 * ‖szegoFactor θ‖ₑ ^ 2 :=
      ((((fourier (-n)).continuous.measurable.sub_const 1).enorm.pow_const 2).mul_const _).mul
        (measurable_szegoFactor.enorm.pow_const 2)
    exact hm.aemeasurable
  rw [lintegral_tsum hmn]
  refine tsum_congr fun n => ?_
  calc ∫⁻ θ, ‖fourier (-n) θ - 1‖ₑ ^ 2 * ‖fourierCoeff a.toFun n‖ₑ ^ 2 * ‖szegoFactor θ‖ₑ ^ 2
        ∂AddCircle.haarAddCircle
      = ∫⁻ θ, ‖fourierCoeff a.toFun n‖ₑ ^ 2 * ‖szegoGeom n θ‖ₑ ^ 2 ∂AddCircle.haarAddCircle := by
        refine lintegral_congr_ae ?_
        filter_upwards [haarAddCircle_ae_ne_zero] with θ hθ
        rw [← szegoGeom_eq n hθ, enorm_mul, mul_pow]
        ring
    _ = (n.natAbs : ℝ≥0∞) * ‖fourierCoeff a.toFun n‖ₑ ^ 2 := by
        rw [lintegral_const_mul _ ((continuous_szegoGeom n).measurable.enorm.pow_const 2),
          lintegral_enorm_szegoGeom_sq, mul_comm]

/-- The weighted energies `∑_n |n| |â(n)|²` of a finite-energy symbol are finite. -/
theorem summable_natAbs_mul_norm_sq (a : CCMCircleHankelSymbol) :
    Summable fun n : ℤ => (n.natAbs : ℝ) * ‖fourierCoeff a.toFun n‖ ^ 2 := by
  refine Summable.of_nat_of_neg_add_one ?_ ?_
  · refine (summable_nat_add_iff 1).1 (a.positiveEnergy.congr fun n => ?_)
    simp only [Int.natAbs_natCast]
  · refine a.negativeEnergy.congr fun n => ?_
    rw [show -((n : ℤ) + 1) = -((n + 1 : ℕ) : ℤ) by push_cast; ring, Int.natAbs_neg,
      Int.natAbs_natCast]

theorem energy_szegoCommutatorKernel_lt_top (a : CCMCircleHankelSymbol) :
    ∫⁻ z, ∫⁻ w, ‖szegoCommutatorKernel a.toFun z w‖ₑ ^ 2 ∂AddCircle.haarAddCircle
      ∂AddCircle.haarAddCircle < ∞ := by
  rw [lintegral_szegoCommutatorKernel]
  have h : ∑' n : ℤ, (n.natAbs : ℝ≥0∞) * ‖fourierCoeff a.toFun n‖ₑ ^ 2 =
      ENNReal.ofReal (∑' n : ℤ, (n.natAbs : ℝ) * ‖fourierCoeff a.toFun n‖ ^ 2) := by
    rw [ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) (summable_natAbs_mul_norm_sq a)]
    refine tsum_congr fun n => ?_
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast, enorm_sq_eq_ofReal]
  rw [h]
  exact ENNReal.ofReal_lt_top

/-- The commutator kernel as a square-integrable kernel on the torus. -/
def szegoCommutatorSqIntKernel (a : CCMCircleHankelSymbol) :
    GaloisForLFunctions.HTGeometry.SqIntKernel (AddCircle.haarAddCircle (T := (1 : ℝ)))
      (AddCircle.haarAddCircle (T := (1 : ℝ))) where
  toFun := szegoCommutatorKernel a.toFun
  measurable := measurable_szegoCommutatorKernel a.measurable
  energy_lt_top := energy_szegoCommutatorKernel_lt_top a

/-! ## The commutator kernel represents `[P, M_a]` -/

theorem integral_fourier_haar (j : ℤ) :
    ∫ x : AddCircle (1 : ℝ), fourier j x ∂AddCircle.haarAddCircle = if j = 0 then 1 else 0 := by
  have h := congr_fun (fourierCoeff_fourier (T := (1 : ℝ)) j) 0
  rw [fourierCoeff] at h
  simpa [fourier_zero, Pi.single_apply, eq_comm] using h

theorem integral_szegoGeom (n : ℤ) :
    ∫ θ, szegoGeom n θ ∂AddCircle.haarAddCircle = if 0 ≤ n then 0 else -1 := by
  have hint : ∀ j : ℤ, Integrable (fun θ : AddCircle (1 : ℝ) => fourier j θ)
      AddCircle.haarAddCircle := fun j =>
    integrableOn_univ.1 ((fourier j).continuous.continuousOn.integrableOn_compact isCompact_univ)
  rcases le_or_gt 0 n with hn | hn
  · simp only [szegoGeom, if_pos hn, szegoNegGeom]
    rw [integral_finsetSum _ fun j _ => hint _]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [integral_fourier_haar, if_neg (by omega)]
  · simp only [szegoGeom, if_neg (not_le.2 hn), szegoPosGeom]
    rw [integral_neg, integral_finsetSum _ fun j _ => hint _]
    have hpos : 0 < (-n).toNat := by omega
    rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.2 hpos)]
    · rw [Nat.cast_zero, integral_fourier_haar, if_pos rfl]
    · intro j _ hj
      rw [integral_fourier_haar, if_neg (by exact_mod_cast hj)]

/-- Energy of the substituted kernel `(a(z - θ) - a(z)) S(θ)` on the torus. -/
theorem lintegral_prod_substituted (a : CCMCircleHankelSymbol) :
    ∫⁻ p : AddCircle (1 : ℝ) × AddCircle (1 : ℝ),
      ‖a.toFun (p.1 - p.2) - a.toFun p.1‖ₑ ^ 2 * ‖szegoFactor p.2‖ₑ ^ 2
        ∂(AddCircle.haarAddCircle.prod AddCircle.haarAddCircle) < ∞ := by
  have hmeasF : Measurable fun p : AddCircle (1 : ℝ) × AddCircle (1 : ℝ) =>
      ‖a.toFun (p.1 - p.2) - a.toFun p.1‖ₑ ^ 2 * ‖szegoFactor p.2‖ₑ ^ 2 :=
    (((a.measurable.comp (measurable_fst.sub measurable_snd)).sub
      (a.measurable.comp measurable_fst)).enorm.pow_const 2).mul
      ((measurable_szegoFactor.comp measurable_snd).enorm.pow_const 2)
  rw [lintegral_prod _ hmeasF.aemeasurable]
  have h1 : ∀ z, ∫⁻ θ, ‖a.toFun (z - θ) - a.toFun z‖ₑ ^ 2 * ‖szegoFactor θ‖ₑ ^ 2
      ∂AddCircle.haarAddCircle =
      ∫⁻ w, ‖szegoCommutatorKernel a.toFun z w‖ₑ ^ 2 ∂AddCircle.haarAddCircle := by
    intro z
    rw [← lintegral_sub_left_eq_self (fun w => ‖szegoCommutatorKernel a.toFun z w‖ₑ ^ 2) z]
    refine lintegral_congr fun θ => ?_
    rw [szegoCommutatorKernel, sub_sub_cancel, enorm_mul, mul_pow]
  simp_rw [h1]
  exact energy_szegoCommutatorKernel_lt_top a

/-- Matrix coefficients of the kernel operator: `⟪e_m, op(c_a) e_n⟫ = ([m ≥ 0] - [n ≥ 0]) â(m - n)`. -/
theorem inner_fourierLp_szegoCommutatorKernel_op (a : CCMCircleHankelSymbol) (m n : ℤ) :
    inner ℂ (fourierLp (T := (1 : ℝ)) 2 m : CCMCircleL2)
        ((szegoCommutatorSqIntKernel a).op (fourierLp (T := (1 : ℝ)) 2 n)) =
      ((if 0 ≤ m then 1 else 0) - (if 0 ≤ n then 1 else 0)) * fourierCoeff a.toFun (m - n) := by
  set μ := (AddCircle.haarAddCircle : Measure (AddCircle (1 : ℝ)))
  rw [GaloisForLFunctions.HTGeometry.SqIntKernel.inner_op]
  -- the input vector is the character `e_n`
  have happly : ∀ z, (szegoCommutatorSqIntKernel a).apply (fourierLp (T := (1 : ℝ)) 2 n) z =
      ∫ θ, (a.toFun (z - θ) - a.toFun z) * szegoFactor θ * fourier n (z - θ) ∂μ := by
    intro z
    rw [GaloisForLFunctions.HTGeometry.SqIntKernel.apply]
    have hae : (fun w => (szegoCommutatorSqIntKernel a).toFun z w *
        (fourierLp (T := (1 : ℝ)) 2 n : CCMCircleL2) w) =ᵐ[μ]
        fun w => szegoCommutatorKernel a.toFun z w * fourier n w := by
      filter_upwards [coeFn_fourierLp (T := (1 : ℝ)) 2 n] with w hw
      rw [hw]; rfl
    rw [integral_congr_ae hae, ← integral_sub_left_eq_self _ μ z]
    refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
    simp only [szegoCommutatorKernel, sub_sub_cancel]
  have hleft : (fun z => starRingEnd ℂ ((fourierLp (T := (1 : ℝ)) 2 m : CCMCircleL2) z) *
      (szegoCommutatorSqIntKernel a).apply (fourierLp (T := (1 : ℝ)) 2 n) z) =ᵐ[μ]
      fun z => ∫ θ, fourier (-m) z * ((a.toFun (z - θ) - a.toFun z) * szegoFactor θ *
        fourier n (z - θ)) ∂μ := by
    filter_upwards [coeFn_fourierLp (T := (1 : ℝ)) 2 m] with z hz
    rw [hz, happly, ← fourier_neg, ← integral_const_mul]
  rw [integral_congr_ae hleft]
  -- Fubini on the torus
  let F : AddCircle (1 : ℝ) → AddCircle (1 : ℝ) → ℂ := fun z θ =>
    fourier (-m) z * ((a.toFun (z - θ) - a.toFun z) * szegoFactor θ * fourier n (z - θ))
  have hFm : Measurable (Function.uncurry F) :=
    ((fourier (-m)).continuous.measurable.comp measurable_fst).mul
      ((((a.measurable.comp (measurable_fst.sub measurable_snd)).sub
        (a.measurable.comp measurable_fst)).mul (measurable_szegoFactor.comp measurable_snd)).mul
        ((fourier n).continuous.measurable.comp (measurable_fst.sub measurable_snd)))
  have hFint : Integrable (Function.uncurry F) (μ.prod μ) := by
    refine ⟨hFm.aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral]
    have hnorm : ∀ p : AddCircle (1 : ℝ) × AddCircle (1 : ℝ), ‖Function.uncurry F p‖ₑ =
        ‖a.toFun (p.1 - p.2) - a.toFun p.1‖ₑ * ‖szegoFactor p.2‖ₑ := by
      intro p
      simp only [Function.uncurry, F, enorm_mul]
      rw [← ofReal_norm (fourier (-m) p.1), norm_fourier_apply_eq_one,
        ← ofReal_norm (fourier n (p.1 - p.2)), norm_fourier_apply_eq_one, ENNReal.ofReal_one]
      ring
    simp_rw [hnorm]
    have hcs := GaloisForLFunctions.HTGeometry.sq_lintegral_mul_le_mul (m := μ.prod μ)
      (a := fun p => ‖a.toFun (p.1 - p.2) - a.toFun p.1‖ₑ * ‖szegoFactor p.2‖ₑ)
      (b := fun _ => 1)
      ((((a.measurable.comp (measurable_fst.sub measurable_snd)).sub
        (a.measurable.comp measurable_fst)).enorm).mul
        ((measurable_szegoFactor.comp measurable_snd).enorm)).aemeasurable aemeasurable_const
    simp only [mul_one, one_pow, lintegral_const, measure_univ] at hcs
    refine GaloisForLFunctions.HTGeometry.lt_top_of_sq_lt_top (hcs.trans_lt ?_)
    simp_rw [mul_pow]
    exact lintegral_prod_substituted a
  rw [integral_integral_swap hFint]
  -- evaluate the inner integral in `z`
  have hneg : ∀ θ : AddCircle (1 : ℝ), fourier n (-θ) = fourier (-n) θ := by
    intro θ; rw [fourier_apply, fourier_apply, smul_neg, neg_smul]
  have hinner : ∀ θ, ∫ z, F z θ ∂μ =
      szegoFactor θ * fourierCoeff a.toFun (m - n) * (fourier (-m) θ - fourier (-n) θ) := by
    intro θ
    have hbd : ∀ (f : AddCircle (1 : ℝ) → ℂ), Measurable f → (∀ z, ‖f z‖ ≤ a.bound) →
        Integrable (fun z => fourier (-(m - n)) z • f z) μ := by
      intro f hf hfb
      refine Integrable.of_bound
        (((fourier (-(m - n))).continuous.measurable).smul hf).aestronglyMeasurable
        a.bound (Eventually.of_forall fun z => ?_)
      rw [norm_smul, norm_fourier_apply_eq_one, one_mul]
      exact hfb z
    have h1 : Integrable (fun z => fourier (-(m - n)) z • a.toFun (z - θ)) μ :=
      hbd _ (a.measurable.comp (measurable_sub_const θ)) fun z => a.norm_le _
    have h2 := hbd _ a.measurable a.norm_le
    have hFeq : (fun z => F z θ) = fun z => (szegoFactor θ * fourier (-n) θ) *
        (fourier (-(m - n)) z • a.toFun (z - θ) - fourier (-(m - n)) z • a.toFun z) := by
      funext z
      simp only [F, smul_eq_mul]
      rw [sub_eq_add_neg z θ, fourier_apply_add, hneg,
        show -(m - n) = -m + n by ring, fourier_add]
      ring
    have ht : ∫ z, fourier (-(m - n)) z • a.toFun (z - θ) ∂μ =
        fourier (-(m - n)) θ * fourierCoeff a.toFun (m - n) :=
      fourierCoeff_translate a.toFun θ (m - n)
    have hc : ∫ z, fourier (-(m - n)) z • a.toFun z ∂μ = fourierCoeff a.toFun (m - n) := rfl
    rw [hFeq, integral_const_mul, integral_sub h1 h2, ht, hc,
      show fourier (-m) θ = fourier (-n) θ * fourier (-(m - n)) θ by
        rw [← fourier_add]; ring_nf]
    ring
  simp_rw [hinner]
  have hae : (fun θ => szegoFactor θ * fourierCoeff a.toFun (m - n) *
      (fourier (-m) θ - fourier (-n) θ)) =ᵐ[μ]
      fun θ => fourierCoeff a.toFun (m - n) * (szegoGeom m θ - szegoGeom n θ) := by
    filter_upwards [haarAddCircle_ae_ne_zero] with θ hθ
    rw [← szegoGeom_eq m hθ, ← szegoGeom_eq n hθ]
    ring
  have hcont : ∀ k : ℤ, Integrable (szegoGeom k) μ := fun k =>
    integrableOn_univ.1 ((continuous_szegoGeom k).continuousOn.integrableOn_compact isCompact_univ)
  rw [integral_congr_ae hae, integral_const_mul, integral_sub (hcont m) (hcont n),
    integral_szegoGeom, integral_szegoGeom]
  split_ifs <;> ring

theorem inner_fourierLp_hardyCommutator (a : CCMCircleBoundedSymbol) (m n : ℤ) :
    inner ℂ (fourierLp (T := (1 : ℝ)) 2 m : CCMCircleL2)
        ((ccmCircleHardyProjection * ccmCircleMultiplier a -
          ccmCircleMultiplier a * ccmCircleHardyProjection) (fourierLp (T := (1 : ℝ)) 2 n)) =
      ((if 0 ≤ m then 1 else 0) - (if 0 ≤ n then 1 else 0)) * fourierCoeff a.toFun (m - n) := by
  rw [sub_apply, inner_sub_right, mul_apply_eq_comp, mul_apply_eq_comp,
    inner_fourierLp_ccmCircleHardyProjection, ccmCircleHardyProjection_fourierLp]
  by_cases hm : 0 ≤ m <;> by_cases hn : 0 ≤ n <;>
    simp [hm, hn, inner_fourierLp_ccmCircleMultiplier]

/-- Bounded operators on circle `L²` are determined by their Fourier matrix coefficients. -/
theorem ext_inner_fourierLp {A B : CCMCircleL2 →L[ℂ] CCMCircleL2}
    (h : ∀ m n : ℤ, inner ℂ (fourierLp (T := (1 : ℝ)) 2 m : CCMCircleL2)
        (A (fourierLp (T := (1 : ℝ)) 2 n)) =
      inner ℂ (fourierLp (T := (1 : ℝ)) 2 m : CCMCircleL2) (B (fourierLp (T := (1 : ℝ)) 2 n))) :
    A = B := by
  refine ContinuousLinearMap.ext_on
    (Submodule.dense_iff_topologicalClosure_eq_top.2 (fourierBasis (T := (1 : ℝ))).dense_span) ?_
  rintro _ ⟨n, rfl⟩
  apply (fourierBasis (T := (1 : ℝ))).repr.injective
  ext m
  rw [(fourierBasis (T := (1 : ℝ))).repr_apply_apply,
    (fourierBasis (T := (1 : ℝ))).repr_apply_apply, fourierBasis_eq_fourierLp,
    fourierBasis_eq_fourierLp]
  exact h m n

/-- **The Szegő commutator kernel represents the Hardy commutator**: `op(c_a) = [P, M_a]`. -/
theorem szegoCommutatorSqIntKernel_op (a : CCMCircleHankelSymbol) :
    (szegoCommutatorSqIntKernel a).op =
      ccmCircleHardyProjection * ccmCircleMultiplier a.toCCMCircleBoundedSymbol -
        ccmCircleMultiplier a.toCCMCircleBoundedSymbol * ccmCircleHardyProjection := by
  refine ext_inner_fourierLp fun m n => ?_
  rw [inner_fourierLp_szegoCommutatorKernel_op, inner_fourierLp_hardyCommutator]

/-! ## Displacement kernels of phases -/

/-- Displacement kernel `d_u(z, w) = (\overline{u(z)} u(w) - 1) S(z - w)`. -/
def szegoDisplacementKernel (u : AddCircle (1 : ℝ) → ℂ) (z w : AddCircle (1 : ℝ)) : ℂ :=
  (starRingEnd ℂ (u z) * u w - 1) * szegoFactor (z - w)

theorem szegoDisplacementKernel_eq (u : HankelCirclePhase) (z w : AddCircle (1 : ℝ)) :
    szegoDisplacementKernel u.toFun z w =
      starRingEnd ℂ (u.toFun z) * szegoCommutatorKernel u.toFun z w := by
  rw [szegoDisplacementKernel, szegoCommutatorKernel, ← mul_assoc, mul_sub, u.conj_mul_self]

theorem measurable_szegoDisplacementKernel {u : AddCircle (1 : ℝ) → ℂ} (hu : Measurable u) :
    Measurable (Function.uncurry (szegoDisplacementKernel u)) :=
  (((Complex.continuous_conj.measurable.comp (hu.comp measurable_fst)).mul
    (hu.comp measurable_snd)).sub_const 1).mul
    (measurable_szegoFactor.comp (measurable_fst.sub measurable_snd))

/-- The displacement kernel of a finite-energy phase as a square-integrable kernel. -/
def szegoDisplacementSqIntKernel (u : HankelCirclePhase) :
    GaloisForLFunctions.HTGeometry.SqIntKernel (AddCircle.haarAddCircle (T := (1 : ℝ)))
      (AddCircle.haarAddCircle (T := (1 : ℝ))) where
  toFun := szegoDisplacementKernel u.toFun
  measurable := measurable_szegoDisplacementKernel u.measurable
  energy_lt_top := by
    have h := energy_szegoCommutatorKernel_lt_top u.toHankelSymbol
    refine lt_of_le_of_lt (le_of_eq ?_) h
    refine lintegral_congr fun z => lintegral_congr fun w => ?_
    rw [szegoDisplacementKernel_eq, enorm_mul, ← ofReal_norm, Complex.norm_conj, u.norm_eq_one,
      ENNReal.ofReal_one, one_mul]
    rfl

/-- **(RUCRI.5)** The phase displacement `M_u† P M_u - P` is the integral operator with kernel
`(\overline{u(z)} u(w) - 1) S(z - w)`. -/
theorem szegoDisplacementSqIntKernel_op (u : HankelCirclePhase) :
    (szegoDisplacementSqIntKernel u).op =
      restrictedProjectionDisplacement u.datum.conjugateProjection u.datum.projection := by
  rw [u.datum.displacement_eq_adjoint_mul_commutator]
  change _ = ContinuousLinearMap.adjoint u.multiplier *
    (ccmCircleHardyProjection * u.multiplier - u.multiplier * ccmCircleHardyProjection)
  rw [u.adjoint_multiplier]
  change _ = ccmCircleMultiplier u.toHankelSymbol.conj.toCCMCircleBoundedSymbol *
    (ccmCircleHardyProjection * ccmCircleMultiplier u.toHankelSymbol.toCCMCircleBoundedSymbol -
      ccmCircleMultiplier u.toHankelSymbol.toCCMCircleBoundedSymbol * ccmCircleHardyProjection)
  rw [← szegoCommutatorSqIntKernel_op]
  ext1 f
  refine Lp.ext ?_
  filter_upwards [(szegoDisplacementSqIntKernel u).op_coeFn f,
    lpBoundedMulCLM_coeFn u.toHankelSymbol.conj.measurable u.toHankelSymbol.conj.bound_nonneg
      u.toHankelSymbol.conj.norm_le ((szegoCommutatorSqIntKernel u.toHankelSymbol).op f),
    (szegoCommutatorSqIntKernel u.toHankelSymbol).op_coeFn f] with z h1 h2 h3
  rw [h1, mul_apply_eq_comp]
  change _ = (ccmCircleMultiplier u.toHankelSymbol.conj.toCCMCircleBoundedSymbol
    ((szegoCommutatorSqIntKernel u.toHankelSymbol).op f) : CCMCircleL2) z
  rw [ccmCircleMultiplier, h2, h3, GaloisForLFunctions.HTGeometry.SqIntKernel.apply,
    GaloisForLFunctions.HTGeometry.SqIntKernel.apply, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  change szegoDisplacementKernel u.toFun z w * _ =
    starRingEnd ℂ (u.toFun z) * (szegoCommutatorKernel u.toFun z w * _)
  rw [szegoDisplacementKernel_eq, mul_assoc]

/-! ## Relative displacement and cubic kernels -/

/-- **(FACHD.9)** Relative displacement kernel
`d_{u,v}(z, w) = (\overline{u(z)} u(w) - \overline{v(z)} v(w)) S(z - w)`. -/
def szegoRelativeKernel (u v : AddCircle (1 : ℝ) → ℂ) (z w : AddCircle (1 : ℝ)) : ℂ :=
  (starRingEnd ℂ (u z) * u w - starRingEnd ℂ (v z) * v w) * szegoFactor (z - w)

theorem szegoRelativeKernel_eq_sub (u v : AddCircle (1 : ℝ) → ℂ) (z w : AddCircle (1 : ℝ)) :
    szegoRelativeKernel u v z w = szegoDisplacementKernel u z w - szegoDisplacementKernel v z w := by
  simp only [szegoRelativeKernel, szegoDisplacementKernel]
  ring

theorem enorm_sub_sq_le (x y : ℂ) : ‖x - y‖ₑ ^ 2 ≤ 2 * ‖x‖ₑ ^ 2 + 2 * ‖y‖ₑ ^ 2 := by
  have hr : ‖x - y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
    nlinarith [norm_sub_le x y, norm_nonneg x, norm_nonneg y, norm_nonneg (x - y),
      sq_nonneg (‖x‖ - ‖y‖)]
  calc ‖x - y‖ₑ ^ 2 = ENNReal.ofReal (‖x - y‖ ^ 2) := enorm_sq_eq_ofReal _
    _ ≤ ENNReal.ofReal (2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2) := ENNReal.ofReal_le_ofReal hr
    _ = 2 * ‖x‖ₑ ^ 2 + 2 * ‖y‖ₑ ^ 2 := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num),
          ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat, enorm_sq_eq_ofReal,
          enorm_sq_eq_ofReal]

/-- The relative displacement kernel as a square-integrable kernel. -/
def szegoRelativeSqIntKernel (u v : HankelCirclePhase) :
    GaloisForLFunctions.HTGeometry.SqIntKernel (AddCircle.haarAddCircle (T := (1 : ℝ)))
      (AddCircle.haarAddCircle (T := (1 : ℝ))) where
  toFun := szegoRelativeKernel u.toFun v.toFun
  measurable := by
    have h := (measurable_szegoDisplacementKernel u.measurable).sub
      (measurable_szegoDisplacementKernel v.measurable)
    have heq : Function.uncurry (szegoRelativeKernel u.toFun v.toFun) =
        Function.uncurry (szegoDisplacementKernel u.toFun) -
          Function.uncurry (szegoDisplacementKernel v.toFun) := by
      funext p; exact szegoRelativeKernel_eq_sub _ _ _ _
    rw [heq]; exact h
  energy_lt_top := by
    let du := szegoDisplacementSqIntKernel u
    let dv := szegoDisplacementSqIntKernel v
    have hbound : ∀ z w, ‖szegoRelativeKernel u.toFun v.toFun z w‖ₑ ^ 2 ≤
        2 * ‖du.toFun z w‖ₑ ^ 2 + 2 * ‖dv.toFun z w‖ₑ ^ 2 := fun z w => by
      rw [szegoRelativeKernel_eq_sub]; exact enorm_sub_sq_le _ _
    refine lt_of_le_of_lt (lintegral_mono fun z => lintegral_mono fun w => hbound z w) ?_
    have hrow : ∀ (k : GaloisForLFunctions.HTGeometry.SqIntKernel
        (AddCircle.haarAddCircle (T := (1 : ℝ))) (AddCircle.haarAddCircle (T := (1 : ℝ)))) (z),
        Measurable fun w => ‖k.toFun z w‖ₑ ^ 2 := fun k z => (k.measurable_left z).enorm.pow_const 2
    have hsplit : ∀ z, ∫⁻ w, (2 * ‖du.toFun z w‖ₑ ^ 2 + 2 * ‖dv.toFun z w‖ₑ ^ 2)
        ∂AddCircle.haarAddCircle =
        2 * du.rowEnergy z + 2 * dv.rowEnergy z := fun z => by
      rw [lintegral_add_left ((hrow du z).const_mul 2), lintegral_const_mul _ (hrow du z),
        lintegral_const_mul _ (hrow dv z)]
      rfl
    simp_rw [hsplit]
    rw [lintegral_add_left (du.measurable_rowEnergy.const_mul 2),
      lintegral_const_mul _ du.measurable_rowEnergy, lintegral_const_mul _ dv.measurable_rowEnergy]
    exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top (by norm_num) du.energy_lt_top,
      ENNReal.mul_lt_top (by norm_num) dv.energy_lt_top⟩

/-- The relative kernel represents `R_u - R_v`. -/
theorem szegoRelativeSqIntKernel_op (u v : HankelCirclePhase) :
    (szegoRelativeSqIntKernel u v).op =
      restrictedProjectionDisplacement u.datum.conjugateProjection v.datum.conjugateProjection := by
  have hsplit : restrictedProjectionDisplacement u.datum.conjugateProjection
        v.datum.conjugateProjection =
      restrictedProjectionDisplacement u.datum.conjugateProjection u.datum.projection -
        restrictedProjectionDisplacement v.datum.conjugateProjection v.datum.projection := by
    simp only [restrictedProjectionDisplacement]
    change _ = (u.datum.conjugateProjection - ccmCircleHardyProjection) -
      (v.datum.conjugateProjection - ccmCircleHardyProjection)
    abel
  rw [hsplit, ← szegoDisplacementSqIntKernel_op, ← szegoDisplacementSqIntKernel_op]
  ext1 f
  refine Lp.ext ?_
  filter_upwards [(szegoRelativeSqIntKernel u v).op_coeFn f,
    (szegoDisplacementSqIntKernel u).op_coeFn f, (szegoDisplacementSqIntKernel v).op_coeFn f,
    Lp.coeFn_sub ((szegoDisplacementSqIntKernel u).op f) ((szegoDisplacementSqIntKernel v).op f),
    (szegoDisplacementSqIntKernel u).ae_integrable f,
    (szegoDisplacementSqIntKernel v).ae_integrable f] with z h1 h2 h3 h4 hiu hiv
  rw [h1, sub_apply, h4, Pi.sub_apply, h2, h3, GaloisForLFunctions.HTGeometry.SqIntKernel.apply,
    GaloisForLFunctions.HTGeometry.SqIntKernel.apply,
    GaloisForLFunctions.HTGeometry.SqIntKernel.apply, ← integral_sub hiu hiv]
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  change szegoRelativeKernel u.toFun v.toFun z w * _ =
    szegoDisplacementKernel u.toFun z w * _ - szegoDisplacementKernel v.toFun z w * _
  rw [szegoRelativeKernel_eq_sub, sub_mul]

/-- **(FACHD.10)** The threefold cyclic kernel `t_{u,v} = d_{u,v} ⋆ d_{u,v} ⋆ d_{u,v}`. -/
def szegoRelativeCubicSqIntKernel (u v : HankelCirclePhase) :
    GaloisForLFunctions.HTGeometry.SqIntKernel (AddCircle.haarAddCircle (T := (1 : ℝ)))
      (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
  ((szegoRelativeSqIntKernel u v).comp (szegoRelativeSqIntKernel u v)).comp
    (szegoRelativeSqIntKernel u v)

theorem szegoRelativeCubicSqIntKernel_toFun (u v : HankelCirclePhase) (z w : AddCircle (1 : ℝ)) :
    (szegoRelativeCubicSqIntKernel u v).toFun z w =
      ∫ z₂, (∫ z₁, szegoRelativeKernel u.toFun v.toFun z z₁ *
          szegoRelativeKernel u.toFun v.toFun z₁ z₂ ∂AddCircle.haarAddCircle) *
        szegoRelativeKernel u.toFun v.toFun z₂ w ∂AddCircle.haarAddCircle :=
  rfl

/-- **(FACHD.10)** The relative cubic defect `(R_u - R_v)³` is the nuclear integral operator with
the threefold cyclic kernel. -/
theorem szegoRelativeCubicSqIntKernel_op (u v : HankelCirclePhase) :
    (szegoRelativeCubicSqIntKernel u v).op =
      restrictedProjectionCubicDefect u.datum.conjugateProjection v.datum.conjugateProjection := by
  rw [szegoRelativeCubicSqIntKernel, GaloisForLFunctions.HTGeometry.SqIntKernel.op_comp,
    GaloisForLFunctions.HTGeometry.SqIntKernel.op_comp, szegoRelativeSqIntKernel_op,
    restrictedProjectionCubicDefect, pow_succ, pow_two]
  rfl

/-- **(RUCRI.6)** The one-endpoint cubic kernel `d_u ⋆ d_u ⋆ d_u`. -/
def szegoCubicSqIntKernel (u : HankelCirclePhase) :
    GaloisForLFunctions.HTGeometry.SqIntKernel (AddCircle.haarAddCircle (T := (1 : ℝ)))
      (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
  ((szegoDisplacementSqIntKernel u).comp (szegoDisplacementSqIntKernel u)).comp
    (szegoDisplacementSqIntKernel u)

theorem szegoCubicSqIntKernel_toFun (u : HankelCirclePhase) (z w : AddCircle (1 : ℝ)) :
    (szegoCubicSqIntKernel u).toFun z w =
      ∫ z₂, (∫ z₁, szegoDisplacementKernel u.toFun z z₁ *
          szegoDisplacementKernel u.toFun z₁ z₂ ∂AddCircle.haarAddCircle) *
        szegoDisplacementKernel u.toFun z₂ w ∂AddCircle.haarAddCircle :=
  rfl

/-- **(RUCRI.6)** `T(M_u) = (M_u† P M_u - P)³` is the nuclear integral operator with kernel
`d_u ⋆ d_u ⋆ d_u`. -/
theorem szegoCubicSqIntKernel_op (u : HankelCirclePhase) :
    (szegoCubicSqIntKernel u).op =
      restrictedProjectionCubicDefect u.datum.conjugateProjection u.datum.projection := by
  rw [szegoCubicSqIntKernel, GaloisForLFunctions.HTGeometry.SqIntKernel.op_comp,
    GaloisForLFunctions.HTGeometry.SqIntKernel.op_comp, szegoDisplacementSqIntKernel_op,
    restrictedProjectionCubicDefect, pow_succ, pow_two]
  rfl

end RHTower
