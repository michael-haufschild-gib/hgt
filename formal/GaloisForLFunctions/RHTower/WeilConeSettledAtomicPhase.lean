import GaloisForLFunctions.RHTower.WeilConeSettledLockRigidity
import GaloisForLFunctions.RHTower.WeilConeNearIntegerAtomicRigidity
import GaloisForLFunctions.RHTower.WeilConeAlmostPeriodicSettledLock
import GaloisForLFunctions.RHTower.WeilConeMixedSpectrumRigidity

/-!
# Atomic spectra whose cumulative mass settles modulo one

Let `lam` be full-cone Weil-positive with purely atomic boundary measure
`μ_lam = Σ_j c_j (δ_{t_j} + δ_{−t_j})` (`t_j ≥ 1`, `t_j → ∞`, `c_j ≥ 0`; ordinates may repeat).  Write
`S(y) = Σ_{t_j < y} c_j` for the cumulative mass.

**Theorem** (`vonMangoldt_and_riemannHypothesis_of_settled_atomic_phase`).  If the phase
`e^{2πiS(y)}` converges to a constant `e^{2πiθ}` at a power rate in mean,

`∫_Y^{2Y} |e^{2πiS(y)} − e^{2πiθ}| dy = O(Y^{1−δ})`,  `δ > 0`,

then `lam(n) = Λ(n)` for every `n ≥ 2`, and the Riemann hypothesis holds.

Compared with `vonMangoldt_and_riemannHypothesis_of_near_integer_atoms`, which needs
`Σ_{t_j<y} |c_j − round(c_j)| = O(y^α)`, the fractional parts may now have linear total size as
long as their cumulative sum settles modulo one.  Example: dipoles, i.e. pairs of atoms with
fractional parts `+a`, `−a` at nearby ordinates whose total separation below `Y` is `O(Y^{1−δ})`.

**Proof.**  The atomic producer `G` (`gInf`) has reflection `G(1 − s) = e^{2πiS(2x)} G(s)` on the
lower critical line (`s = ½ − 2ix`).  Its Herglotz form agrees with `weilContinuation` on
`Re s > 1`, hence on `Re s > ½` (`eqOn_weilContinuation`).  So `power_settled_lock_rigidity`
applies.
-/

open Complex Set Filter MeasureTheory Topology
open scoped ComplexConjugate

noncomputable section

namespace RHTower.WeilSpectral

open WeilHerglotz IntegerMassRigidity FractionalMassRigidity FractionalMassTailRigidity
  AbelianTwist PhaseLockRigidity

/-- A holomorphic `Φ` on `Re s > ½` that agrees with the Weil function on `Re s > 1` is the Weil
continuation. -/
theorem eqOn_weilContinuation {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {Φ : ℂ → ℂ}
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hid : ∀ s : ℂ, 1 < s.re → Φ s = zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (lamTwo lam) s) {s : ℂ} (hs : 1 / 2 < s.re) : Φ s = weilContinuation hW s := by
  set U : Set ℂ := {s : ℂ | 1 / 2 < s.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have h2 : (2 : ℂ) ∈ U := by show (1 / 2 : ℝ) < (2 : ℂ).re; norm_num
  have hev : Φ =ᶠ[𝓝 (2 : ℂ)] weilContinuation hW := by
    have hV : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (show (1 : ℝ) < (2 : ℂ).re by norm_num)
    filter_upwards [hV] with z hz
    rw [hid z hz, weilContinuation_eq_lamTwo hW hz]
  exact (hΦd.analyticOnNhd hUo).eqOn_of_preconnected_of_eventuallyEq
    ((differentiableOn_weilContinuation hW).analyticOnNhd hUo)
    (convex_halfSpace_re_gt (1 / 2)).isPreconnected h2 hev hs

/-- **Atomic spectra whose cumulative mass settles modulo one force `Λ` and RH.** -/
theorem vonMangoldt_and_riemannHypothesis_of_settled_atomic_phase {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) {c t : ℕ → ℝ} (hc : ∀ j, 0 ≤ c j) (hone : ∀ j, 1 ≤ t j)
    (htt : Tendsto t atTop atTop) (hsum : Summable fun j => c j / t j ^ 2)
    (hrep : ∀ w : ℂ, 0 < w.re → ∫⁻ r, poissonDensity w r ∂boundaryMeasure hW =
      ∑' j, ENNReal.ofReal (c j) * (poissonDensity w (t j) + poissonDensity w (-(t j))))
    {θ δ Cm Y₁ : ℝ} (hδ : 0 < δ)
    (hsettle : ∀ Y : ℝ, Y₁ ≤ Y → ∫ y in Ioc Y (2 * Y),
      ‖cexp (((2 * Real.pi * phaseSum c t y : ℝ) : ℂ) * I) -
        cexp (((2 * Real.pi * θ : ℝ) : ℂ) * I)‖ ≤ Cm * Y ^ (1 - δ)) :
    (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis := by
  have hsl := fun (σ : ℝ) (hσ : 1 < σ) =>
    WeilMeanSquare.summable_abs_div_rpow_of_weilPositiveFull hW hσ
  have hid0 := weilFunction_eq_atomicPairSeries hW hc hone hsum hrep
  have hsum0 : Summable fun j => ((fun _ => (0 : ℕ)) j : ℝ) / t j ^ 2 := by simp
  set m : ℕ → ℕ := fun _ => 0 with hm
  set G := gInf lam m t c t with hGdef
  set Φ := phiInf m t c t with hΦdef
  have hidΦ : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s := by
    intro s hs
    have h := hid0 s hs
    rw [weilFunction] at h
    have hfun : lamTwo lam = lamC lam := by
      funext n; unfold lamTwo lamC; split_ifs <;> simp
    show atomicPairSeries (fun j => Real.pi * (m j : ℝ)) t s +
      ∑' k, (c k : ℂ) * (2 * (s - 1 / 2) / ((s - 1 / 2) ^ 2 + (t k : ℂ) ^ 2)) = _
    simp only [hm, Nat.cast_zero, mul_zero]
    have h0 : atomicPairSeries (fun _ => (0 : ℝ)) t s = 0 := by unfold atomicPairSeries; simp
    rw [h0, zero_add, ← atomicPairSeries_pi_mul_eq, ← h, zetaArchimedeanDatum, hfun]
  have hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re} :=
    differentiableOn_phiInf lam hone hsum0 hc hone htt hsum
  have hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s := fun s hs =>
    continuousAt_gInf hone hsum0 hc hone htt hsum hs
  have hGd' : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s := fun s hs =>
    hasDerivAt_gInf hone hsum0 hc hone htt hsum hs
  have hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (weilContinuation hW s * G s) s := by
    intro s hs
    rw [← eqOn_weilContinuation hW hΦd hidΦ hs]
    exact hGd' s hs
  have hG2 : G 2 = bigG lam 2 := gInf_two hone hsum0 hc hone htt hsum
  -- the lock
  set w : ℝ → ℂ := fun τ => cexp (((2 * Real.pi * phaseSum c t (-(2 * τ)) : ℝ) : ℂ) * I) with hw
  have hlock : ∀ τ : ℝ, τ < -0 → G (1 - lineS τ) = w τ * G (lineS τ) := by
    intro τ hτ0
    rw [neg_zero] at hτ0
    have hy : 0 < -(2 * τ) := by linarith
    have hline : lineS τ = 1 / 2 - ((-(2 * τ) : ℝ) : ℂ) * I := by
      rw [lineS_eq]; push_cast; ring
    have hre : (1 / 2 : ℝ) ≤ (lineS τ).re := le_of_eq (lineS_re τ).symm
    simp only [hGdef, gInf, hw]
    rw [atomQ_one_sub hone hsum0, one_sub_lineS_eq_conj, fracInfProd_conj hc hone htt hsum hre,
      hline, conj_fracInfProd_lower hc hone htt hsum hy]
    ring
  have hwm : Measurable w := by
    have hph : Measurable fun τ : ℝ => phaseSum c t (-(2 * τ)) :=
      ((phaseSum_mono hc htt).comp_antitone (show Antitone fun τ : ℝ => -(2 * τ) from
        fun a b hab => by linarith)).measurable
    exact Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp
      (measurable_const.mul hph)).mul_const I)
  have hwb : ∀ τ, ‖w τ‖ ≤ 1 := fun τ => by
    simp only [hw, Complex.norm_exp_ofReal_mul_I, le_refl]
  set c₀ : ℂ := (cexp (((2 * Real.pi * θ : ℝ) : ℂ) * I))⁻¹ with hc₀
  have hc₀0 : c₀ ≠ 0 := inv_ne_zero (Complex.exp_ne_zero _)
  refine power_settled_lock_rigidity hW hGc hGd hG2 hwm hwb hc₀0 le_rfl hlock
    (Cm := max Cm 0) (T₁ := max Y₁ 1) hδ fun T hT => ?_
  -- change of variables `y = 2τ`
  have hT1 : 1 ≤ T := (le_max_right _ _).trans hT
  have hT0 : 0 < T := by linarith
  have hY : Y₁ ≤ 2 * T := by have := (le_max_left Y₁ 1).trans hT; linarith
  set f : ℝ → ℝ := fun y => ‖cexp (((2 * Real.pi * phaseSum c t y : ℝ) : ℂ) * I) -
    cexp (((2 * Real.pi * θ : ℝ) : ℂ) * I)‖ with hf
  have hfeq : ∀ τ : ℝ, ‖w (-τ) - c₀⁻¹‖ = f (2 * τ) := by
    intro τ
    simp only [hw, hc₀, inv_inv, hf]
    congr 4
    ring_nf
  simp only [hfeq]
  have hfm : Measurable f := by
    have hph : Measurable fun y : ℝ => phaseSum c t y := (phaseSum_mono hc htt).measurable
    exact ((Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp
      (measurable_const.mul hph)).mul_const I)).sub_const _).norm
  have hchange : ∫ τ in Ioc T (2 * T), f (2 * τ) =
      2⁻¹ * ∫ y in Ioc (2 * T) (2 * (2 * T)), f y := by
    rw [← intervalIntegral.integral_of_le (by linarith),
      ← intervalIntegral.integral_of_le (by linarith),
      intervalIntegral.integral_comp_mul_left f (by norm_num : (2 : ℝ) ≠ 0), smul_eq_mul]
  rw [hchange]
  have h := hsettle (2 * T) hY
  have h2 : (2 * T) ^ (1 - δ) ≤ 2 * T ^ (1 - δ) := by
    rw [Real.mul_rpow (by norm_num) hT0.le]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    rcases le_or_gt (1 - δ) 0 with hd | hd
    · exact (Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) hd).trans (by norm_num)
    · calc (2 : ℝ) ^ (1 - δ) ≤ 2 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 2 := Real.rpow_one 2
  calc 2⁻¹ * ∫ y in Ioc (2 * T) (2 * (2 * T)), f y ≤ 2⁻¹ * (Cm * (2 * T) ^ (1 - δ)) :=
        mul_le_mul_of_nonneg_left h (by norm_num)
    _ ≤ 2⁻¹ * (max Cm 0 * (2 * T ^ (1 - δ))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        calc Cm * (2 * T) ^ (1 - δ) ≤ max Cm 0 * (2 * T) ^ (1 - δ) :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
          _ ≤ max Cm 0 * (2 * T ^ (1 - δ)) :=
              mul_le_mul_of_nonneg_left h2 (le_max_right _ _)
    _ = max Cm 0 * T ^ (1 - δ) := by ring


theorem apFactor_two_mul (p : ℕ → ℂ) (ω : ℕ → ℝ) (x : ℝ) :
    apFactor p ω (2 * x) = apFactor p (fun j => 2 * ω j) x := by
  unfold apFactor
  congr 1; funext j
  rw [show ω j * (2 * x) = 2 * ω j * x by ring]

/-- **Atomic spectra whose cumulative phase is almost periodic up to a power-small error.**  In the
setting of `vonMangoldt_and_riemannHypothesis_of_settled_atomic_phase`, suppose instead that
`∫_Y^{2Y} |e^{2πiS(y)} − P(y)| dy = O(Y^{1−δ})` for an almost-periodic
`P(y) = Σ_j p_j e^{iλ_j y}` with `Σ |p_j| e^{|λ_j|} < ∞` and no nonzero frequency with
`e^{−λ_j} ∈ ℚ_{>0}`.  Then the mean of `P` is nonzero, `lam = Λ` and RH holds. -/
theorem vonMangoldt_and_riemannHypothesis_of_ap_settled_atomic_phase {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) {c t : ℕ → ℝ} (hc : ∀ j, 0 ≤ c j) (hone : ∀ j, 1 ≤ t j)
    (htt : Tendsto t atTop atTop) (hsum : Summable fun j => c j / t j ^ 2)
    (hrep : ∀ w : ℂ, 0 < w.re → ∫⁻ r, poissonDensity w r ∂boundaryMeasure hW =
      ∑' j, ENNReal.ofReal (c j) * (poissonDensity w (t j) + poissonDensity w (-(t j))))
    {p : ℕ → ℂ} {ϖ : ℕ → ℝ} (hp : Summable fun j => ‖p j‖ * Real.exp |ϖ j|)
    (hres : ∀ j, ϖ j ≠ 0 → ∀ m n : ℕ, 1 ≤ m → (n : ℝ) ≠ m * Real.exp (-(ϖ j)))
    {δ Cm Y₁ : ℝ} (hδ : 0 < δ)
    (hsettle : ∀ Y : ℝ, Y₁ ≤ Y → ∫ y in Ioc Y (2 * Y),
      ‖cexp (((2 * Real.pi * phaseSum c t y : ℝ) : ℂ) * I) - apFactor p ϖ y‖ ≤
        Cm * Y ^ (1 - δ)) :
    apMean p ϖ ≠ 0 ∧ (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧
      RiemannHypothesis := by
  have hid0 := weilFunction_eq_atomicPairSeries hW hc hone hsum hrep
  have hsum0 : Summable fun j => ((fun _ => (0 : ℕ)) j : ℝ) / t j ^ 2 := by simp
  set m : ℕ → ℕ := fun _ => 0 with hm
  set G := gInf lam m t c t with hGdef
  set Φ := phiInf m t c t with hΦdef
  have hidΦ : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s := by
    intro s hs
    have h := hid0 s hs
    rw [weilFunction] at h
    have hfun : lamTwo lam = lamC lam := by
      funext n; unfold lamTwo lamC; split_ifs <;> simp
    show atomicPairSeries (fun j => Real.pi * (m j : ℝ)) t s +
      ∑' k, (c k : ℂ) * (2 * (s - 1 / 2) / ((s - 1 / 2) ^ 2 + (t k : ℂ) ^ 2)) = _
    simp only [hm, Nat.cast_zero, mul_zero]
    have h0 : atomicPairSeries (fun _ => (0 : ℝ)) t s = 0 := by unfold atomicPairSeries; simp
    rw [h0, zero_add, ← atomicPairSeries_pi_mul_eq, ← h, zetaArchimedeanDatum, hfun]
  have hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re} :=
    differentiableOn_phiInf lam hone hsum0 hc hone htt hsum
  have hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s := fun s hs =>
    continuousAt_gInf hone hsum0 hc hone htt hsum hs
  have hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (weilContinuation hW s * G s) s := by
    intro s hs
    rw [← eqOn_weilContinuation hW hΦd hidΦ hs]
    exact hasDerivAt_gInf hone hsum0 hc hone htt hsum hs
  have hG2 : G 2 = bigG lam 2 := gInf_two hone hsum0 hc hone htt hsum
  -- the remainder
  set S : ℝ → ℝ := phaseSum c t with hS
  set r : ℝ → ℂ := fun x => cexp (((2 * Real.pi * S (2 * x) : ℝ) : ℂ) * I) -
    apFactor p ϖ (2 * x) with hr
  have hp1 : Summable fun j => ‖p j‖ := (summable_norm_of_exp (ω := ϖ) (p := p)
    (hp.of_nonneg_of_le (fun j => by positivity) fun j => mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by linarith [abs_nonneg (ϖ j)])) (norm_nonneg _)))
  have hSm : Measurable S := (phaseSum_mono hc htt).measurable
  have hrm : Measurable r := by
    refine (Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp
      (measurable_const.mul (hSm.comp (measurable_const_mul 2)))).mul_const I)).sub ?_
    exact ((continuous_apFactor hp1).comp (continuous_const_mul 2)).measurable
  have hrb : ∀ x, ‖r x‖ ≤ 1 + ∑' j, ‖p j‖ := fun x => by
    simp only [hr]
    refine (norm_sub_le _ _).trans ?_
    rw [Complex.norm_exp_ofReal_mul_I]
    have := norm_apFactor_le hp1 (ω := ϖ) (2 * x)
    linarith
  have hlock : ∀ τ : ℝ, τ < -1 → G (1 - lineS τ) =
      1 * (apFactor p (fun j => 2 * ϖ j) (-τ) + r (-τ)) * G (lineS τ) := by
    intro τ hτ
    have hτ0 : τ < 0 := by linarith
    have hy : 0 < -(2 * τ) := by linarith
    have hline : lineS τ = 1 / 2 - ((-(2 * τ) : ℝ) : ℂ) * I := by
      rw [lineS_eq]; push_cast; ring
    have hre : (1 / 2 : ℝ) ≤ (lineS τ).re := le_of_eq (lineS_re τ).symm
    have hrefl : G (1 - lineS τ) =
        cexp (((2 * Real.pi * phaseSum c t (-(2 * τ)) : ℝ) : ℂ) * I) * G (lineS τ) := by
      simp only [hGdef, gInf]
      rw [atomQ_one_sub hone hsum0, one_sub_lineS_eq_conj, fracInfProd_conj hc hone htt hsum hre,
        hline, conj_fracInfProd_lower hc hone htt hsum hy]
      ring
    rw [hrefl, one_mul, ← apFactor_two_mul]
    simp only [hr, hS]
    rw [show 2 * -τ = -(2 * τ) by ring, add_sub_cancel]
  have hp2 : Summable fun j => ‖p j‖ * Real.exp (|2 * ϖ j| / 2) := by
    refine hp.congr fun j => ?_
    rw [abs_mul, abs_two, mul_div_cancel_left₀ _ (two_ne_zero)]
  have hres2 : ∀ j, 2 * ϖ j ≠ 0 → ∀ m n : ℕ, 1 ≤ m →
      (n : ℝ) ≠ m * Real.exp (-(2 * ϖ j / 2)) := by
    intro j hj m n hm
    rw [mul_div_cancel_left₀ _ (two_ne_zero)]
    exact hres j (fun h => hj (by rw [h, mul_zero])) m n hm
  have h := ap_power_settled_lock_rigidity hW hGc hGd hG2 hp2 hres2 hrm hrb hlock
    (Cm := max Cm 0) (T₁ := max Y₁ 1) hδ fun T hT => ?_
  · have hmean : apMean p (fun j => 2 * ϖ j) = apMean p ϖ := by
      unfold apMean
      congr 1; funext j
      by_cases hj : ϖ j = 0
      · simp [hj]
      · rw [if_neg (by intro h0; exact hj (by linarith)), if_neg hj]
    rw [one_mul, hmean] at h
    exact h
  · have hT1 : 1 ≤ T := (le_max_right _ _).trans hT
    have hT0 : 0 < T := by linarith
    have hY : Y₁ ≤ 2 * T := by have := (le_max_left Y₁ 1).trans hT; linarith
    set f : ℝ → ℝ := fun y => ‖cexp (((2 * Real.pi * phaseSum c t y : ℝ) : ℂ) * I) -
      apFactor p ϖ y‖ with hf
    have hfeq : ∀ x : ℝ, ‖r x‖ = f (2 * x) := fun x => rfl
    simp only [hfeq]
    have hchange : ∫ x in Ioc T (2 * T), f (2 * x) =
        2⁻¹ * ∫ y in Ioc (2 * T) (2 * (2 * T)), f y := by
      rw [← intervalIntegral.integral_of_le (by linarith),
        ← intervalIntegral.integral_of_le (by linarith),
        intervalIntegral.integral_comp_mul_left f (by norm_num : (2 : ℝ) ≠ 0), smul_eq_mul]
    rw [hchange]
    have h1 := hsettle (2 * T) hY
    have h2 : (2 * T) ^ (1 - δ) ≤ 2 * T ^ (1 - δ) := by
      rw [Real.mul_rpow (by norm_num) hT0.le]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      rcases le_or_gt (1 - δ) 0 with hd | hd
      · exact (Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) hd).trans (by norm_num)
      · calc (2 : ℝ) ^ (1 - δ) ≤ 2 ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
          _ = 2 := Real.rpow_one 2
    calc 2⁻¹ * ∫ y in Ioc (2 * T) (2 * (2 * T)), f y ≤ 2⁻¹ * (Cm * (2 * T) ^ (1 - δ)) :=
          mul_le_mul_of_nonneg_left h1 (by norm_num)
      _ ≤ 2⁻¹ * (max Cm 0 * (2 * T ^ (1 - δ))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          calc Cm * (2 * T) ^ (1 - δ) ≤ max Cm 0 * (2 * T) ^ (1 - δ) :=
                mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
            _ ≤ max Cm 0 * (2 * T ^ (1 - δ)) :=
                mul_le_mul_of_nonneg_left h2 (le_max_right _ _)
      _ = max Cm 0 * T ^ (1 - δ) := by ring


/-- **Approximately integer spectral counting forces `Λ` and RH (mixed spectra).**  Let `lam` be
full-cone Weil-positive with boundary measure = integer atoms + real atoms `c_k` at `u_k` + a
positive rest `ν`, the diffuse part `Φ_d` of the Weil continuation being continuous up to the line.
The spectral phase is `θ(y) = 2π Σ_{u_k<y} c_k + 2∫_{−y}^{0} Re Φ_d(½+iv) dv`, i.e. `2π` times the
non-integer spectral mass below `y`.  If `e^{iθ(y)}` settles to a constant at a power rate in mean,
`∫_Y^{2Y} |e^{iθ(y)} − e^{2πiθ₀}| dy = O(Y^{1−δ})`, then `lam = Λ` and RH holds.

This is the approximate form of integer-counting rigidity
(`vonMangoldt_and_riemannHypothesis_of_integer_counting`). -/
theorem vonMangoldt_and_riemannHypothesis_of_settled_mixed_phase {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) {m : ℕ → ℕ} {t c u : ℕ → ℝ} (hone : ∀ j, 1 ≤ t j)
    (hsum : Summable fun j => (m j : ℝ) / t j ^ 2) (hc : ∀ k, 0 ≤ c k) (hu1 : ∀ k, 1 ≤ u k)
    (hut : Tendsto u atTop atTop) (hcs2 : Summable fun k => c k / u k ^ 2) {ν : Measure ℝ}
    (hrep : ∀ w : ℂ, 0 < w.re → ∫⁻ r, poissonDensity w r ∂boundaryMeasure hW =
      (∑' j, ENNReal.ofReal (m j) * (poissonDensity w (t j) + poissonDensity w (-(t j)))) +
      (∑' k, ENNReal.ofReal (c k) * (poissonDensity w (u k) + poissonDensity w (-(u k)))) +
      ∫⁻ r, poissonDensity w r ∂ν)
    {Φd : ℂ → ℂ} (hΦdc : ContinuousOn Φd {s : ℂ | 1 / 2 ≤ s.re})
    (hΦdeq : ∀ s : ℂ, 1 / 2 < s.re → weilContinuation hW s =
      atomicPairSeries (fun j => Real.pi * m j) t s +
        (∑' k, (c k : ℂ) * (2 * (s - 1 / 2) / ((s - 1 / 2) ^ 2 + (u k : ℂ) ^ 2))) + Φd s)
    {θ₀ δ Cm Y₁ : ℝ} (hδ : 0 < δ)
    (hsettle : ∀ Y : ℝ, Y₁ ≤ Y → ∫ y in Ioc Y (2 * Y),
      ‖cexp (((2 * Real.pi * phaseSum c u y +
          2 * ∫ v in -y..0, (Φd ((1 / 2 : ℂ) + (v : ℂ) * I)).re : ℝ) : ℂ) * I) -
        cexp (((2 * Real.pi * θ₀ : ℝ) : ℂ) * I)‖ ≤ Cm * Y ^ (1 - δ)) :
    (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis := by
  obtain ⟨hΦdd, hΦdre, hid⟩ := mixed_spectrum_data hW hone hsum hc hu1 hcs2 hrep hΦdeq
  obtain ⟨Φ, G, hΦd, -, hidΦ, hGc, hGd', hG2, hlock⟩ :=
    exists_producer_of_mixed_spectrum hone hsum hc hu1 hut hcs2 hΦdd hΦdc hΦdre hid
  have hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (weilContinuation hW s * G s) s := by
    intro s hs
    rw [← eqOn_weilContinuation hW hΦd hidΦ hs]
    exact hGd' s hs
  -- the phase
  set I₀ : ℝ → ℝ := fun y => ∫ v in -y..0, (Φd ((1 / 2 : ℂ) + (v : ℂ) * I)).re with hI₀
  have hcontΦ : Continuous fun v : ℝ => (Φd ((1 / 2 : ℂ) + (v : ℂ) * I)).re := by
    refine Complex.continuous_re.comp (hΦdc.comp_continuous (by fun_prop) fun v => ?_)
    show (1 / 2 : ℝ) ≤ ((1 / 2 : ℂ) + (v : ℂ) * I).re
    simp
  have hI₀c : Continuous I₀ := by
    have h := intervalIntegral.continuous_primitive (μ := volume)
      (fun a b => hcontΦ.intervalIntegrable a b) 0
    have e : I₀ = fun y => -∫ v in (0 : ℝ)..(-y), (Φd ((1 / 2 : ℂ) + (v : ℂ) * I)).re := by
      funext y; simp only [hI₀]; rw [intervalIntegral.integral_symm]
    rw [e]
    exact (h.comp continuous_neg).neg
  set θ : ℝ → ℝ := fun y => 2 * Real.pi * phaseSum c u y + 2 * I₀ y with hθ
  have hθm : Measurable θ :=
    (measurable_const.mul (phaseSum_mono hc hut).measurable).add
      (measurable_const.mul hI₀c.measurable)
  set w : ℝ → ℂ := fun τ => cexp (((θ (-(2 * τ)) : ℝ) : ℂ) * I) with hw
  have hlock' : ∀ τ : ℝ, τ < -0 → G (1 - lineS τ) = w τ * G (lineS τ) := by
    intro τ hτ
    rw [neg_zero] at hτ
    rw [hlock τ hτ]
  have hwm : Measurable w :=
    Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp
      (hθm.comp (measurable_const_mul 2).neg)).mul_const I)
  have hwb : ∀ τ, ‖w τ‖ ≤ 1 := fun τ => by simp only [hw, Complex.norm_exp_ofReal_mul_I, le_refl]
  set c₀ : ℂ := (cexp (((2 * Real.pi * θ₀ : ℝ) : ℂ) * I))⁻¹ with hc₀
  have hc₀0 : c₀ ≠ 0 := inv_ne_zero (Complex.exp_ne_zero _)
  refine power_settled_lock_rigidity hW hGc hGd hG2 hwm hwb hc₀0 le_rfl hlock'
    (Cm := max Cm 0) (T₁ := max Y₁ 1) hδ fun T hT => ?_
  have hT1 : 1 ≤ T := (le_max_right _ _).trans hT
  have hT0 : 0 < T := by linarith
  have hY : Y₁ ≤ 2 * T := by have := (le_max_left Y₁ 1).trans hT; linarith
  set f : ℝ → ℝ := fun y => ‖cexp (((θ y : ℝ) : ℂ) * I) -
    cexp (((2 * Real.pi * θ₀ : ℝ) : ℂ) * I)‖ with hf
  have hfeq : ∀ τ : ℝ, ‖w (-τ) - c₀⁻¹‖ = f (2 * τ) := by
    intro τ
    simp only [hw, hc₀, inv_inv, hf]
    rw [show -(2 * -τ) = 2 * τ by ring]
  simp only [hfeq]
  have hchange : ∫ τ in Ioc T (2 * T), f (2 * τ) =
      2⁻¹ * ∫ y in Ioc (2 * T) (2 * (2 * T)), f y := by
    rw [← intervalIntegral.integral_of_le (by linarith),
      ← intervalIntegral.integral_of_le (by linarith),
      intervalIntegral.integral_comp_mul_left f (by norm_num : (2 : ℝ) ≠ 0), smul_eq_mul]
  rw [hchange]
  have h1 := hsettle (2 * T) hY
  have h2 : (2 * T) ^ (1 - δ) ≤ 2 * T ^ (1 - δ) := by
    rw [Real.mul_rpow (by norm_num) hT0.le]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    rcases le_or_gt (1 - δ) 0 with hd | hd
    · exact (Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) hd).trans (by norm_num)
    · calc (2 : ℝ) ^ (1 - δ) ≤ 2 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 2 := Real.rpow_one 2
  calc 2⁻¹ * ∫ y in Ioc (2 * T) (2 * (2 * T)), f y ≤ 2⁻¹ * (Cm * (2 * T) ^ (1 - δ)) :=
        mul_le_mul_of_nonneg_left h1 (by norm_num)
    _ ≤ 2⁻¹ * (max Cm 0 * (2 * T ^ (1 - δ))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        calc Cm * (2 * T) ^ (1 - δ) ≤ max Cm 0 * (2 * T) ^ (1 - δ) :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
          _ ≤ max Cm 0 * (2 * T ^ (1 - δ)) :=
              mul_le_mul_of_nonneg_left h2 (le_max_right _ _)
    _ = max Cm 0 * T ^ (1 - δ) := by ring


/-- **Euler class: approximate integer counting at a log-power rate.**  In the setting of
`vonMangoldt_and_riemannHypothesis_of_settled_mixed_phase`, if moreover `|lam(n)| ≤ κ log n` and
the rest weight is summable, the mean-square rate
`∫_Y^{2Y} |e^{iθ(y)} − e^{iθ₀}|² dy = O(Y (log Y)^{−κ²−η})` suffices. -/
theorem vonMangoldt_and_riemannHypothesis_of_log_settled_mixed_phase {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) (hA : Summable (restWeight lam)) {κ : ℝ} (hκ : 0 ≤ κ)
    (hlam : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ κ * Real.log n)
    {m : ℕ → ℕ} {t c u : ℕ → ℝ} (hone : ∀ j, 1 ≤ t j)
    (hsum : Summable fun j => (m j : ℝ) / t j ^ 2) (hc : ∀ k, 0 ≤ c k) (hu1 : ∀ k, 1 ≤ u k)
    (hut : Tendsto u atTop atTop) (hcs2 : Summable fun k => c k / u k ^ 2) {ν : Measure ℝ}
    (hrep : ∀ w : ℂ, 0 < w.re → ∫⁻ r, poissonDensity w r ∂boundaryMeasure hW =
      (∑' j, ENNReal.ofReal (m j) * (poissonDensity w (t j) + poissonDensity w (-(t j)))) +
      (∑' k, ENNReal.ofReal (c k) * (poissonDensity w (u k) + poissonDensity w (-(u k)))) +
      ∫⁻ r, poissonDensity w r ∂ν)
    {Φd : ℂ → ℂ} (hΦdc : ContinuousOn Φd {s : ℂ | 1 / 2 ≤ s.re})
    (hΦdeq : ∀ s : ℂ, 1 / 2 < s.re → weilContinuation hW s =
      atomicPairSeries (fun j => Real.pi * m j) t s +
        (∑' k, (c k : ℂ) * (2 * (s - 1 / 2) / ((s - 1 / 2) ^ 2 + (u k : ℂ) ^ 2))) + Φd s)
    {θ₀ η Cm Y₁ : ℝ} (hη : 0 < η)
    (hsettle : ∀ Y : ℝ, Y₁ ≤ Y → ∫ y in Ioc Y (2 * Y),
      ‖cexp (((2 * Real.pi * phaseSum c u y +
          2 * ∫ v in -y..0, (Φd ((1 / 2 : ℂ) + (v : ℂ) * I)).re : ℝ) : ℂ) * I) -
        cexp (((2 * Real.pi * θ₀ : ℝ) : ℂ) * I)‖ ^ 2 ≤ Cm * Y * Real.log Y ^ (-(κ ^ 2 + η))) :
    (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis := by
  obtain ⟨hΦdd, hΦdre, hid⟩ := mixed_spectrum_data hW hone hsum hc hu1 hcs2 hrep hΦdeq
  obtain ⟨Φ, G, hΦd, -, hidΦ, hGc, hGd', hG2, hlock⟩ :=
    exists_producer_of_mixed_spectrum hone hsum hc hu1 hut hcs2 hΦdd hΦdc hΦdre hid
  have hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (weilContinuation hW s * G s) s := by
    intro s hs
    rw [← eqOn_weilContinuation hW hΦd hidΦ hs]
    exact hGd' s hs
  set I₀ : ℝ → ℝ := fun y => ∫ v in -y..0, (Φd ((1 / 2 : ℂ) + (v : ℂ) * I)).re with hI₀
  have hcontΦ : Continuous fun v : ℝ => (Φd ((1 / 2 : ℂ) + (v : ℂ) * I)).re := by
    refine Complex.continuous_re.comp (hΦdc.comp_continuous (by fun_prop) fun v => ?_)
    show (1 / 2 : ℝ) ≤ ((1 / 2 : ℂ) + (v : ℂ) * I).re
    simp
  have hI₀c : Continuous I₀ := by
    have h := intervalIntegral.continuous_primitive (μ := volume)
      (fun a b => hcontΦ.intervalIntegrable a b) 0
    have e : I₀ = fun y => -∫ v in (0 : ℝ)..(-y), (Φd ((1 / 2 : ℂ) + (v : ℂ) * I)).re := by
      funext y; simp only [hI₀]; rw [intervalIntegral.integral_symm]
    rw [e]
    exact (h.comp continuous_neg).neg
  set θ : ℝ → ℝ := fun y => 2 * Real.pi * phaseSum c u y + 2 * I₀ y with hθ
  have hθm : Measurable θ :=
    (measurable_const.mul (phaseSum_mono hc hut).measurable).add
      (measurable_const.mul hI₀c.measurable)
  set w : ℝ → ℂ := fun τ => cexp (((θ (-(2 * τ)) : ℝ) : ℂ) * I) with hw
  have hlock' : ∀ τ : ℝ, τ < -0 → G (1 - lineS τ) = w τ * G (lineS τ) := by
    intro τ hτ
    rw [neg_zero] at hτ
    rw [hlock τ hτ]
  have hwm : Measurable w :=
    Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp
      (hθm.comp (measurable_const_mul 2).neg)).mul_const I)
  have hwb : ∀ τ, ‖w τ‖ ≤ 1 := fun τ => by simp only [hw, Complex.norm_exp_ofReal_mul_I, le_refl]
  set c₀ : ℂ := (cexp (((2 * Real.pi * θ₀ : ℝ) : ℂ) * I))⁻¹ with hc₀
  have hc₀0 : c₀ ≠ 0 := inv_ne_zero (Complex.exp_ne_zero _)
  refine settled_lock_rigidity hW hA hκ hlam hGc hGd hG2 hwm hwb hc₀0 le_rfl hlock'
    (Cm := 2 * max Cm 0) (T₁ := max Y₁ 2) hη fun T hT => ?_
  have hT2 : 2 ≤ T := (le_max_right _ _).trans hT
  have hT0 : 0 < T := by linarith
  have hY : Y₁ ≤ 2 * T := by have := (le_max_left Y₁ 2).trans hT; linarith
  set f : ℝ → ℝ := fun y => ‖cexp (((θ y : ℝ) : ℂ) * I) -
    cexp (((2 * Real.pi * θ₀ : ℝ) : ℂ) * I)‖ ^ 2 with hf
  have hfeq : ∀ τ : ℝ, ‖w (-τ) - c₀⁻¹‖ ^ 2 = f (2 * τ) := by
    intro τ
    simp only [hw, hc₀, inv_inv, hf]
    rw [show -(2 * -τ) = 2 * τ by ring]
  simp only [hfeq]
  have hchange : ∫ τ in Ioc T (2 * T), f (2 * τ) =
      2⁻¹ * ∫ y in Ioc (2 * T) (2 * (2 * T)), f y := by
    rw [← intervalIntegral.integral_of_le (by linarith),
      ← intervalIntegral.integral_of_le (by linarith),
      intervalIntegral.integral_comp_mul_left f (by norm_num : (2 : ℝ) ≠ 0), smul_eq_mul]
  rw [hchange]
  have h1 := hsettle (2 * T) hY
  have hlogT : 0 < Real.log T := Real.log_pos (by linarith)
  have hlog : Real.log T ≤ Real.log (2 * T) := Real.log_le_log hT0 (by linarith)
  have hpow : Real.log (2 * T) ^ (-(κ ^ 2 + η)) ≤ Real.log T ^ (-(κ ^ 2 + η)) :=
    Real.rpow_le_rpow_of_nonpos hlogT hlog (by nlinarith [sq_nonneg κ])
  calc 2⁻¹ * ∫ y in Ioc (2 * T) (2 * (2 * T)), f y
      ≤ 2⁻¹ * (Cm * (2 * T) * Real.log (2 * T) ^ (-(κ ^ 2 + η))) :=
        mul_le_mul_of_nonneg_left h1 (by norm_num)
    _ ≤ 2⁻¹ * (max Cm 0 * (2 * T) * Real.log T ^ (-(κ ^ 2 + η))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        calc Cm * (2 * T) * Real.log (2 * T) ^ (-(κ ^ 2 + η))
            ≤ max Cm 0 * (2 * T) * Real.log (2 * T) ^ (-(κ ^ 2 + η)) := by
              gcongr
              · exact (Real.rpow_pos_of_pos (by linarith [hlog]) _).le
              · exact le_max_left _ _
          _ ≤ max Cm 0 * (2 * T) * Real.log T ^ (-(κ ^ 2 + η)) :=
              mul_le_mul_of_nonneg_left hpow (by positivity)
    _ ≤ 2 * max Cm 0 * T * Real.log T ^ (-(κ ^ 2 + η)) := by
        have : 0 ≤ max Cm 0 * T * Real.log T ^ (-(κ ^ 2 + η)) := by positivity
        nlinarith

end RHTower.WeilSpectral
