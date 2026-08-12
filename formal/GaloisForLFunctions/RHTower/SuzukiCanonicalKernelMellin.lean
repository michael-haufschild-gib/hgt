import GaloisForLFunctions.RHTower.SuzukiMellinConvolution
import GaloisForLFunctions.RHTower.SuzukiGammaMultiplierPassivity
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

open Complex MeasureTheory Set

noncomputable section

namespace RHTower

/-- The unit-interval beta tail used in Suzuki's kernel. -/
def suzukiOneMinusKernel (omega : ℝ) : ℝ → ℂ :=
  indicator (Ioc (0 : ℝ) 1) fun x =>
    (1 - (x : ℂ)) ^ ((omega : ℂ) - 1)

theorem measurable_suzukiOneMinusKernel (omega : ℝ) :
    Measurable (suzukiOneMinusKernel omega) := by
  exact (by fun_prop : Measurable fun x : ℝ =>
    (1 - (x : ℂ)) ^ ((omega : ℂ) - 1)).indicator measurableSet_Ioc

/-- Beta integral as an exact Mellin transform. -/
theorem hasMellin_suzukiOneMinusKernel
    {omega : ℝ} (homega : 0 < omega) {q : ℂ} (hq : 0 < q.re) :
    HasMellin (suzukiOneMinusKernel omega) q
      (Complex.betaIntegral q (omega : ℂ)) := by
  have hbeta := Complex.betaIntegral_convergent (u := q) (v := (omega : ℂ))
    hq (by simpa using homega)
  constructor
  · rw [MellinConvergent]
    have hint : IntegrableOn (fun x : ℝ =>
        (x : ℂ) ^ (q - 1) *
          (1 - (x : ℂ)) ^ ((omega : ℂ) - 1)) (Ioc 0 1) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp hbeta
    have hind : Integrable
        (indicator (Ioc (0 : ℝ) 1) fun x : ℝ =>
          (x : ℂ) ^ (q - 1) *
            (1 - (x : ℂ)) ^ ((omega : ℂ) - 1)) :=
      (integrable_indicator_iff measurableSet_Ioc).mpr hint
    have hrestrict : IntegrableOn
        (indicator (Ioc (0 : ℝ) 1) fun x : ℝ =>
          (x : ℂ) ^ (q - 1) *
            (1 - (x : ℂ)) ^ ((omega : ℂ) - 1)) (Ioi 0) :=
      hind.integrableOn
    convert hrestrict using 1
    funext x
    simp only [suzukiOneMinusKernel, smul_eq_mul, indicator]
    split_ifs <;> simp
  · rw [mellin, suzukiOneMinusKernel, Complex.betaIntegral,
      intervalIntegral.integral_of_le zero_le_one]
    simp only [smul_eq_mul]
    rw [← integral_indicator measurableSet_Ioi,
      ← integral_indicator measurableSet_Ioc]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ Ioc (0 : ℝ) 1
    · have hx' : x ∈ Ioi (0 : ℝ) := Ioc_subset_Ioi_self hx
      simp [indicator, hx, hx']
    · simp [indicator, hx]

/-- Suzuki's first compact beta kernel, normalized so its Mellin transform is a Gamma ratio. -/
def suzukiPrimaryBetaKernel (omega : ℝ) : ℝ → ℂ := fun x =>
  (2 / Complex.Gamma (omega : ℂ)) *
      (x : ℂ) ^ ((2 - omega : ℝ) : ℂ) *
      suzukiOneMinusKernel omega (x ^ (2 : ℝ))

theorem measurable_suzukiPrimaryBetaKernel (omega : ℝ) :
    Measurable (suzukiPrimaryBetaKernel omega) := by
  unfold suzukiPrimaryBetaKernel
  apply Measurable.mul
  · fun_prop
  · exact (measurable_suzukiOneMinusKernel omega).comp (by fun_prop)

theorem hasMellin_suzukiPrimaryBetaKernel
    {omega : ℝ} (homega : 0 < omega) {s : ℂ} (hs : omega - 2 < s.re) :
    HasMellin (suzukiPrimaryBetaKernel omega) s
      (Complex.Gamma ((s - (omega : ℂ)) / 2 + 1) /
        Complex.Gamma ((s + (omega : ℂ)) / 2 + 1)) := by
  let a : ℂ := ((2 - omega : ℝ) : ℂ)
  let q : ℂ := (s + a) / 2
  have hq : 0 < q.re := by
    dsimp only [q, a]
    norm_num
    linarith
  have hbase := hasMellin_suzukiOneMinusKernel homega hq
  have hcompconv : MellinConvergent
      (fun x : ℝ => suzukiOneMinusKernel omega (x ^ (2 : ℝ))) (s + a) := by
    exact (MellinConvergent.comp_rpow (f := suzukiOneMinusKernel omega)
      (s := s + a) (a := 2) (by norm_num)).2 (by simpa [q] using hbase.1)
  have hpowconv : MellinConvergent
      (fun x : ℝ => (x : ℂ) ^ a *
        suzukiOneMinusKernel omega (x ^ (2 : ℝ))) s := by
    simpa only [smul_eq_mul] using
      (MellinConvergent.cpow_smul (f := fun x : ℝ =>
        suzukiOneMinusKernel omega (x ^ (2 : ℝ))) (s := s) (a := a)).2 hcompconv
  have hconst := hpowconv.const_smul (2 / Complex.Gamma (omega : ℂ))
  constructor
  · refine hconst.congr ?_
    filter_upwards with x
    simp only [suzukiPrimaryBetaKernel, a, smul_eq_mul]
    ring
  · rw [show suzukiPrimaryBetaKernel omega = fun x : ℝ =>
        (2 / Complex.Gamma (omega : ℂ)) •
          ((x : ℂ) ^ a * suzukiOneMinusKernel omega (x ^ (2 : ℝ))) by
        funext x
        simp only [suzukiPrimaryBetaKernel, a, smul_eq_mul]
        ring,
      mellin_const_smul]
    change (2 / Complex.Gamma (omega : ℂ)) *
        mellin (fun x : ℝ => (x : ℂ) ^ a •
          suzukiOneMinusKernel omega (x ^ (2 : ℝ))) s = _
    rw [mellin_cpow_smul, mellin_comp_rpow]
    norm_num
    rw [show (s + a) / 2 = q by rfl, hbase.2,
      Complex.betaIntegral_eq_Gamma_mul_div q (omega : ℂ) hq (by simpa using homega)]
    have hGammaOmega : Complex.Gamma (omega : ℂ) ≠ 0 :=
      Complex.Gamma_ne_zero_of_re_pos (by simpa using homega)
    have hqeq : q = (s - (omega : ℂ)) / 2 + 1 := by
      dsimp only [q, a]
      push_cast
      ring
    have hqomega : q + (omega : ℂ) = (s + (omega : ℂ)) / 2 + 1 := by
      dsimp only [q, a]
      push_cast
      ring
    rw [hqeq]
    have hden : (s - (omega : ℂ)) / 2 + 1 + (omega : ℂ) =
        (s + (omega : ℂ)) / 2 + 1 := by ring
    rw [hden]
    field_simp

/-- The compact pole kernel whose Mellin transform is `(s + omega - 1)^{-1}`. -/
def suzukiPoleKernel (omega : ℝ) : ℝ → ℂ :=
  indicator (Ioc (0 : ℝ) 1) fun x =>
    (x : ℂ) ^ ((omega - 1 : ℝ) : ℂ)

theorem measurable_suzukiPoleKernel (omega : ℝ) :
    Measurable (suzukiPoleKernel omega) := by
  exact (by fun_prop : Measurable fun x : ℝ =>
    (x : ℂ) ^ ((omega - 1 : ℝ) : ℂ)).indicator measurableSet_Ioc

theorem hasMellin_suzukiPoleKernel
    {omega : ℝ} {s : ℂ} (hs : 1 - omega < s.re) :
    HasMellin (suzukiPoleKernel omega) s
      (1 / (s + (omega : ℂ) - 1)) := by
  have hpos : 0 < s.re + ((omega - 1 : ℝ) : ℂ).re := by
    norm_num
    linarith
  have h := hasMellin_cpow_Ioc (((omega - 1 : ℝ) : ℂ) : ℂ) hpos
  have heq : (((omega - 1 : ℝ) : ℂ) : ℂ) = (omega : ℂ) - 1 := by
    push_cast
    rfl
  rw [heq] at h
  rw [show suzukiPoleKernel omega =
      indicator (Ioc (0 : ℝ) 1) fun x => (x : ℂ) ^ ((omega : ℂ) - 1) by
    funext x
    simp only [suzukiPoleKernel]
    rw [heq]]
  simpa only [sub_eq_add_neg, add_assoc] using h

/-- On the positive half-line, the beta--pole convolution has exactly the source's truncated
integral (automatically zero when `x ≥ 1`). -/
theorem positiveMellinConvolution_primary_pole_eq_integral
    (omega : ℝ) {x : ℝ} (hx0 : 0 < x) :
    positiveMellinConvolution
        (suzukiPrimaryBetaKernel omega) (suzukiPoleKernel omega) x =
      ∫ y in Ioc x 1,
        ((2 / Complex.Gamma (omega : ℂ)) *
            (y : ℂ) ^ ((2 - omega : ℝ) : ℂ) *
            (1 - (y : ℂ) ^ (2 : ℕ)) ^ ((omega : ℂ) - 1)) *
          ((x / y : ℝ) : ℂ) ^ ((omega - 1 : ℝ) : ℂ) / y := by
  rw [positiveMellinConvolution, ← integral_indicator measurableSet_Ioi,
    ← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  filter_upwards [volume.ae_ne x] with y hyne
  by_cases hy0 : 0 < y
  · by_cases hyx : x < y
    · by_cases hy1 : y ≤ 1
      · have hySq : y ^ (2 : ℝ) ∈ Ioc (0 : ℝ) 1 := by
          rw [Real.rpow_two]
          constructor <;> nlinarith
        have hxy : x / y ∈ Ioc (0 : ℝ) 1 := by
          constructor
          · positivity
          · exact (div_le_one hy0).mpr hyx.le
        have hy0mem : y ∈ Ioi (0 : ℝ) := hy0
        have hymem : y ∈ Ioc x 1 := ⟨hyx, hy1⟩
        rw [Set.indicator_of_mem hy0mem, Set.indicator_of_mem hymem,
          suzukiPrimaryBetaKernel, suzukiOneMinusKernel,
          Set.indicator_of_mem hySq, suzukiPoleKernel,
          Set.indicator_of_mem hxy, Real.rpow_two, Complex.ofReal_pow]
      · have hySq : y ^ (2 : ℝ) ∉ Ioc (0 : ℝ) 1 := by
          rw [Real.rpow_two]
          intro h
          nlinarith [h.2]
        have hnot : y ∉ Ioc x 1 := fun h => hy1 h.2
        have hy0mem : y ∈ Ioi (0 : ℝ) := hy0
        rw [Set.indicator_of_mem hy0mem, Set.indicator_of_notMem hnot,
          suzukiPrimaryBetaKernel, suzukiOneMinusKernel,
          Set.indicator_of_notMem hySq]
        simp
    · have hxy : x / y ∉ Ioc (0 : ℝ) 1 := by
        intro h
        have : y < x := lt_of_le_of_ne (le_of_not_gt hyx) hyne
        have : 1 < x / y := (one_lt_div hy0).mpr this
        linarith [h.2]
      have hnot : y ∉ Ioc x 1 := fun h => hyx h.1
      have hy0mem : y ∈ Ioi (0 : ℝ) := hy0
      rw [Set.indicator_of_mem hy0mem, Set.indicator_of_notMem hnot,
        suzukiPoleKernel, Set.indicator_of_notMem hxy]
      simp
  · have hnot0 : y ∉ Ioi (0 : ℝ) := hy0
    have hnot : y ∉ Ioc x 1 := by
      intro h
      exact hy0 (lt_trans hx0 h.1)
    simp [hnot0, hnot]

/-- Exact square substitution in the incomplete-beta tail occurring in Suzuki's source formula. -/
theorem suzuki_square_substitution
    (omega : ℝ) {x : ℝ} (hx0 : 0 < x) :
    (∫ y in Ioc x 1,
        (2 * y : ℝ) •
          (((y ^ 2 : ℝ) : ℂ) ^ ((1 / 2 - omega : ℝ) : ℂ) *
            (1 - ((y ^ 2 : ℝ) : ℂ)) ^ ((omega : ℂ) - 1))) =
      ∫ t in Ioc (x ^ 2) 1,
        (t : ℂ) ^ ((1 / 2 - omega : ℝ) : ℂ) *
          (1 - (t : ℂ)) ^ ((omega : ℂ) - 1) := by
  let F : ℝ → ℂ := fun t =>
    (t : ℂ) ^ ((1 / 2 - omega : ℝ) : ℂ) *
      (1 - (t : ℂ)) ^ ((omega : ℂ) - 1)
  let G : ℝ → ℂ := indicator (Ioc (x ^ 2) 1) F
  have h := MeasureTheory.integral_comp_rpow_Ioi (g := G) (p := (2 : ℝ)) (by norm_num)
  convert h using 1
  · rw [show Ioc x 1 = Ioi (0 : ℝ) ∩ Ioc x 1 by
        ext y
        simp only [mem_Ioc, mem_inter_iff, mem_Ioi]
        constructor
        · intro hy
          exact ⟨lt_trans hx0 hy.1, hy⟩
        · exact fun hy => hy.2,
      ← setIntegral_indicator measurableSet_Ioc]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y hy0
    have hy0' : 0 < y := hy0
    by_cases hymem : y ∈ Ioc x 1
    · have hySq : y ^ (2 : ℝ) ∈ Ioc (x ^ 2) 1 := by
        rw [Real.rpow_two]
        constructor
        · exact (sq_lt_sq₀ hx0.le hy0'.le).2 hymem.1
        · simpa only [one_pow] using
            (sq_le_sq₀ hy0'.le zero_le_one).2 hymem.2
      dsimp only [G]
      rw [Set.indicator_of_mem hymem, Set.indicator_of_mem hySq]
      dsimp only [F]
      rw [Real.rpow_two]
      norm_num
    · have hySq : y ^ (2 : ℝ) ∉ Ioc (x ^ 2) 1 := by
        rw [Real.rpow_two]
        intro hSq
        apply hymem
        exact ⟨(sq_lt_sq₀ hx0.le hy0'.le).1 hSq.1,
          (sq_le_sq₀ hy0'.le zero_le_one).1 (by simpa only [one_pow] using hSq.2)⟩
      dsimp only [G]
      rw [Set.indicator_of_notMem hymem, Set.indicator_of_notMem hySq]
      simp
  · dsimp only [G]
    rw [setIntegral_indicator measurableSet_Ioc,
      show Ioi (0 : ℝ) ∩ Ioc (x ^ 2) 1 = Ioc (x ^ 2) 1 by
        ext t
        simp only [mem_inter_iff, mem_Ioi, mem_Ioc]
        constructor
        · exact fun ht => ht.2
        · intro ht
          exact ⟨lt_of_lt_of_le (sq_pos_of_pos hx0) ht.1.le, ht⟩]

/-- Suzuki's literal incomplete-beta tail. -/
def suzukiBetaTail (omega x : ℝ) : ℂ :=
  ∫ t in Ioc (x ^ 2) 1,
    (t : ℂ) ^ ((1 / 2 - omega : ℝ) : ℂ) *
      (1 - (t : ℂ)) ^ ((omega : ℂ) - 1)

/-- The convolution term is exactly the incomplete-beta term printed in Suzuki (2012). -/
theorem positiveMellinConvolution_primary_pole_eq_betaTail
    (omega : ℝ) {x : ℝ} (hx0 : 0 < x) :
    positiveMellinConvolution
        (suzukiPrimaryBetaKernel omega) (suzukiPoleKernel omega) x =
      (x : ℂ) ^ ((omega - 1 : ℝ) : ℂ) /
          Complex.Gamma (omega : ℂ) * suzukiBetaTail omega x := by
  rw [positiveMellinConvolution_primary_pole_eq_integral omega hx0,
    suzukiBetaTail, ← suzuki_square_substitution omega hx0, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro y hy
  have hy0 : 0 < y := lt_trans hx0 hy.1
  have hreal :
      y ^ (2 - omega : ℝ) * (x / y) ^ (omega - 1 : ℝ) / y =
        x ^ (omega - 1 : ℝ) *
          (y * (y ^ 2) ^ (1 / 2 - omega : ℝ)) := by
    have hleft :
        y ^ (2 - omega : ℝ) / y ^ (omega - 1 : ℝ) / y =
          y ^ (2 - 2 * omega : ℝ) := by
      calc
        y ^ (2 - omega) / y ^ (omega - 1) / y =
            y ^ ((2 - omega) - (omega - 1)) / y := by
              exact congrArg (fun z : ℝ => z / y)
                (Real.rpow_sub hy0 (2 - omega) (omega - 1)).symm
        _ = y ^ ((2 - omega) - (omega - 1)) / y ^ (1 : ℝ) := by
              rw [Real.rpow_one]
        _ = y ^ (((2 - omega) - (omega - 1)) - 1) := by
              exact (Real.rpow_sub hy0 ((2 - omega) - (omega - 1)) 1).symm
        _ = y ^ (2 - 2 * omega) := by
              congr 1
              ring
    have hright :
        y * (y ^ 2) ^ (1 / 2 - omega : ℝ) =
          y ^ (2 - 2 * omega : ℝ) := by
      have hsquare :
          (y ^ (2 : ℕ)) ^ (1 / 2 - omega : ℝ) =
            y ^ ((2 : ℝ) * (1 / 2 - omega)) := by
        rw [← Real.rpow_two]
        exact (Real.rpow_mul hy0.le 2 (1 / 2 - omega)).symm
      calc
        y * (y ^ 2) ^ (1 / 2 - omega) =
            y * y ^ (2 * (1 / 2 - omega)) := by rw [hsquare]
        _ = y ^ (1 : ℝ) * y ^ (2 * (1 / 2 - omega)) := by
              rw [Real.rpow_one]
        _ = y ^ (1 + 2 * (1 / 2 - omega)) := by
              exact (Real.rpow_add hy0 1 (2 * (1 / 2 - omega))).symm
        _ = y ^ (2 - 2 * omega) := by
              congr 1
              ring
    rw [Real.div_rpow hx0.le hy0.le]
    calc
      y ^ (2 - omega) * (x ^ (omega - 1) / y ^ (omega - 1)) / y =
          x ^ (omega - 1) *
            (y ^ (2 - omega) / y ^ (omega - 1) / y) := by ring
      _ = x ^ (omega - 1) * y ^ (2 - 2 * omega) := by rw [hleft]
      _ = x ^ (omega - 1) * (y * (y ^ 2) ^ (1 / 2 - omega)) := by rw [hright]
  have hrealC := congrArg (fun r : ℝ => (r : ℂ)) hreal
  dsimp only
  rw [← Complex.ofReal_cpow hy0.le (2 - omega),
    ← Complex.ofReal_cpow (div_nonneg hx0.le hy0.le) (omega - 1),
    ← Complex.ofReal_cpow hx0.le (omega - 1),
    ← Complex.ofReal_cpow (sq_nonneg y) (1 / 2 - omega)]
  push_cast at hrealC
  simp only [Complex.real_smul, Complex.ofReal_pow]
  push_cast
  linear_combination
    (2 / Complex.Gamma (omega : ℂ) *
      (1 - (y : ℂ) ^ (2 : ℕ)) ^ ((omega : ℂ) - 1)) * hrealC

/-- On the source interval, the normalized primary kernel is Suzuki's first beta density. -/
theorem suzukiPrimaryBetaKernel_eq_source
    (omega : ℝ) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    suzukiPrimaryBetaKernel omega x =
      (2 / Complex.Gamma (omega : ℂ)) *
        (x : ℂ) ^ ((2 - omega : ℝ) : ℂ) *
          (1 - (x : ℂ) ^ (2 : ℕ)) ^ ((omega : ℂ) - 1) := by
  have hxSq : x ^ (2 : ℝ) ∈ Ioc (0 : ℝ) 1 := by
    rw [Real.rpow_two]
    constructor <;> nlinarith
  rw [suzukiPrimaryBetaKernel, suzukiOneMinusKernel,
    Set.indicator_of_mem hxSq, Real.rpow_two, Complex.ofReal_pow]

/-- Literal beta--convolution kernel behind Suzuki (2012), equation (204). -/
def suzukiCanonicalG (omega : ℝ) : ℝ → ℂ := fun x =>
  (Real.pi : ℂ) ^ (omega : ℂ) * suzukiPrimaryBetaKernel omega x -
    ((2 * omega : ℝ) : ℂ) * (Real.pi : ℂ) ^ (omega : ℂ) *
      positiveMellinConvolution
        (suzukiPrimaryBetaKernel omega) (suzukiPoleKernel omega) x

/-- **Literal Suzuki kernel formula.**  This is the displayed definition of `g_omega(x)` in
Suzuki (2012), including its incomplete-beta integral, for `0 < x < 1`. -/
theorem suzukiCanonicalG_eq_source
    (omega : ℝ) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    suzukiCanonicalG omega x =
      (2 * (Real.pi : ℂ) ^ (omega : ℂ) /
          Complex.Gamma (omega : ℂ)) *
        ((x : ℂ) ^ ((2 - omega : ℝ) : ℂ) *
            (1 - (x : ℂ) ^ (2 : ℕ)) ^ ((omega : ℂ) - 1) -
          (omega : ℂ) * (x : ℂ) ^ ((omega - 1 : ℝ) : ℂ) *
            suzukiBetaTail omega x) := by
  rw [suzukiCanonicalG, suzukiPrimaryBetaKernel_eq_source omega hx0 hx1,
    positiveMellinConvolution_primary_pole_eq_betaTail omega hx0]
  push_cast
  ring

theorem suzukiBetaTail_eq_zero_of_one_lt
    (omega : ℝ) {x : ℝ} (hx : 1 < x) :
    suzukiBetaTail omega x = 0 := by
  rw [suzukiBetaTail, show Ioc (x ^ 2) 1 = ∅ by
    ext t
    simp only [mem_Ioc, mem_empty_iff_false, iff_false]
    intro ht
    nlinarith [sq_lt_sq₀ zero_le_one (by positivity : 0 ≤ x) |>.2 hx]]
  simp

theorem suzukiPrimaryBetaKernel_eq_zero_of_one_lt
    (omega : ℝ) {x : ℝ} (hx : 1 < x) :
    suzukiPrimaryBetaKernel omega x = 0 := by
  have hxSq : x ^ (2 : ℝ) ∉ Ioc (0 : ℝ) 1 := by
    rw [Real.rpow_two]
    intro h
    nlinarith [sq_lt_sq₀ zero_le_one (by positivity : 0 ≤ x) |>.2 hx, h.2]
  rw [suzukiPrimaryBetaKernel, suzukiOneMinusKernel,
    Set.indicator_of_notMem hxSq]
  simp

/-- The canonical convolution kernel has the exact support asserted in Suzuki's definition. -/
theorem suzukiCanonicalG_eq_zero_of_one_lt
    (omega : ℝ) {x : ℝ} (hx : 1 < x) :
    suzukiCanonicalG omega x = 0 := by
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  rw [suzukiCanonicalG, suzukiPrimaryBetaKernel_eq_zero_of_one_lt omega hx,
    positiveMellinConvolution_primary_pole_eq_betaTail omega hx0,
    suzukiBetaTail_eq_zero_of_one_lt omega hx]
  ring

/-- Source-faithful totalization of Suzuki's `g_omega`; the undefined endpoint `x = 1` is set
to zero, which is immaterial to every Lebesgue/Mellin statement. -/
def suzukiSourceG (omega : ℝ) (x : ℝ) : ℂ :=
  if 0 < x ∧ x < 1 then
    (2 * (Real.pi : ℂ) ^ (omega : ℂ) /
        Complex.Gamma (omega : ℂ)) *
      ((x : ℂ) ^ ((2 - omega : ℝ) : ℂ) *
          (1 - (x : ℂ) ^ (2 : ℕ)) ^ ((omega : ℂ) - 1) -
        (omega : ℂ) * (x : ℂ) ^ ((omega - 1 : ℝ) : ℂ) *
          suzukiBetaTail omega x)
  else 0

theorem suzukiCanonicalG_ae_eq_sourceG (omega : ℝ) :
    suzukiCanonicalG omega =ᵐ[volume.restrict (Ioi (0 : ℝ))] suzukiSourceG omega := by
  filter_upwards [ae_restrict_mem measurableSet_Ioi,
    MeasureTheory.ae_restrict_of_ae (volume.ae_ne 1)] with x hx0 hx1
  by_cases hxlt : x < 1
  · rw [suzukiSourceG, if_pos ⟨hx0, hxlt⟩]
    exact suzukiCanonicalG_eq_source omega hx0 hxlt
  · have hxgt : 1 < x := lt_of_le_of_ne (le_of_not_gt hxlt) (Ne.symm hx1)
    have hnot : ¬(0 < x ∧ x < 1) := fun h => hxlt h.2
    rw [suzukiCanonicalG_eq_zero_of_one_lt omega hxgt,
      suzukiSourceG, if_neg hnot]

/-- Source equation (301)--(302) before simplifying the archimedean factor ratio. -/
theorem hasMellin_suzukiCanonicalG_explicit
    {omega : ℝ} (homega : 0 < omega) {s : ℂ}
    (hs1 : omega - 2 < s.re) (hs2 : 1 - omega < s.re) :
    HasMellin (suzukiCanonicalG omega) s
      ((Real.pi : ℂ) ^ (omega : ℂ) *
          (Complex.Gamma ((s - (omega : ℂ)) / 2 + 1) /
            Complex.Gamma ((s + (omega : ℂ)) / 2 + 1)) -
        ((2 * omega : ℝ) : ℂ) * (Real.pi : ℂ) ^ (omega : ℂ) *
          ((Complex.Gamma ((s - (omega : ℂ)) / 2 + 1) /
              Complex.Gamma ((s + (omega : ℂ)) / 2 + 1)) *
            (1 / (s + (omega : ℂ) - 1)))) := by
  let R : ℂ := Complex.Gamma ((s - (omega : ℂ)) / 2 + 1) /
    Complex.Gamma ((s + (omega : ℂ)) / 2 + 1)
  have hp := hasMellin_suzukiPrimaryBetaKernel homega hs1
  have hb := hasMellin_suzukiPoleKernel (s := s) hs2
  have hc := hasMellin_positiveMellinConvolution
    (measurable_suzukiPrimaryBetaKernel omega)
    (measurable_suzukiPoleKernel omega) hp.1 hb.1
  have hleft := hasMellin_const_smul hp.1 ((Real.pi : ℂ) ^ (omega : ℂ))
  have hright := hasMellin_const_smul hc.1
    (((2 * omega : ℝ) : ℂ) * (Real.pi : ℂ) ^ (omega : ℂ))
  have hsub := hasMellin_sub hleft.1 hright.1
  constructor
  · refine hsub.1.congr ?_
    filter_upwards with x
    simp only [suzukiCanonicalG, smul_eq_mul]
  · rw [show suzukiCanonicalG omega = fun x : ℝ =>
        (Real.pi : ℂ) ^ (omega : ℂ) • suzukiPrimaryBetaKernel omega x -
          ((((2 * omega : ℝ) : ℂ) * (Real.pi : ℂ) ^ (omega : ℂ)) •
            positiveMellinConvolution
              (suzukiPrimaryBetaKernel omega) (suzukiPoleKernel omega) x) by
        funext x
        simp only [suzukiCanonicalG, smul_eq_mul],
      hsub.2, hleft.2, hright.2, hc.2, hp.2, hb.2]
    simp only [smul_eq_mul]

/-- Algebraic Gamma-recursion step identifying Suzuki's explicit transform with the
archimedean-factor quotient. -/
theorem suzukiCanonicalGammaExpression_eq_archimedeanFactorRatio
    {omega : ℝ} (homega : 0 < omega) {s : ℂ} (hs : 1 + omega < s.re) :
    (Real.pi : ℂ) ^ (omega : ℂ) *
          (Complex.Gamma ((s - (omega : ℂ)) / 2 + 1) /
            Complex.Gamma ((s + (omega : ℂ)) / 2 + 1)) -
        ((2 * omega : ℝ) : ℂ) * (Real.pi : ℂ) ^ (omega : ℂ) *
          ((Complex.Gamma ((s - (omega : ℂ)) / 2 + 1) /
              Complex.Gamma ((s + (omega : ℂ)) / 2 + 1)) *
            (1 / (s + (omega : ℂ) - 1))) =
      suzukiArchimedeanFactor (s - (omega : ℂ)) /
        suzukiArchimedeanFactor (s + (omega : ℂ)) := by
  have hsm : s - (omega : ℂ) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
    linarith
  have hsp : s + (omega : ℂ) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
    linarith
  have hsm1 : s - (omega : ℂ) - 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
    linarith
  have hsp1 : s + (omega : ℂ) - 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
    linarith
  have hgm : (s - (omega : ℂ)) / 2 ≠ 0 := div_ne_zero hsm (by norm_num)
  have hgp : (s + (omega : ℂ)) / 2 ≠ 0 := div_ne_zero hsp (by norm_num)
  have hGm : Complex.Gamma ((s - (omega : ℂ)) / 2) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by norm_num; linarith)
  have hGp : Complex.Gamma ((s + (omega : ℂ)) / 2) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by norm_num; linarith)
  have hpi0 : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hpi :
      (Real.pi : ℂ) ^ (-(s - (omega : ℂ)) / 2) /
          (Real.pi : ℂ) ^ (-(s + (omega : ℂ)) / 2) =
        (Real.pi : ℂ) ^ (omega : ℂ) := by
    rw [← Complex.cpow_sub _ _ hpi0]
    congr 1
    ring
  rw [Complex.Gamma_add_one _ hgm, Complex.Gamma_add_one _ hgp,
    suzukiArchimedeanFactor, suzukiArchimedeanFactor]
  rw [show -(s - (omega : ℂ)) / 2 = -(s - (omega : ℂ)) / 2 by rfl,
    show -(s + (omega : ℂ)) / 2 = -(s + (omega : ℂ)) / 2 by rfl]
  field_simp
  rw [← hpi]
  field_simp
  push_cast
  ring

/-- Exact Mellin transform of Suzuki's canonical compact kernel. -/
theorem hasMellin_suzukiCanonicalG
    {omega : ℝ} (homega : 0 < omega) {s : ℂ} (hs : 1 + omega < s.re) :
    HasMellin (suzukiCanonicalG omega) s
      (suzukiArchimedeanFactor (s - (omega : ℂ)) /
        suzukiArchimedeanFactor (s + (omega : ℂ))) := by
  rw [← suzukiCanonicalGammaExpression_eq_archimedeanFactorRatio homega hs]
  exact hasMellin_suzukiCanonicalG_explicit homega (by linarith) (by linarith)

/-- Source equation following (302), now for the literal incomplete-beta kernel `g_omega`. -/
theorem hasMellin_suzukiSourceG
    {omega : ℝ} (homega : 0 < omega) {s : ℂ} (hs : 1 + omega < s.re) :
    HasMellin (suzukiSourceG omega) s
      (suzukiArchimedeanFactor (s - (omega : ℂ)) /
        suzukiArchimedeanFactor (s + (omega : ℂ))) := by
  have h := hasMellin_suzukiCanonicalG homega hs
  have hae := suzukiCanonicalG_ae_eq_sourceG omega
  constructor
  · refine h.1.congr ?_
    filter_upwards [hae] with x hx
    rw [hx]
  · rw [mellin]
    calc
      (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) • suzukiSourceG omega t) =
          ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) • suzukiCanonicalG omega t := by
            apply integral_congr_ae
            filter_upwards [hae] with x hx
            rw [hx]
      _ = suzukiArchimedeanFactor (s - (omega : ℂ)) /
          suzukiArchimedeanFactor (s + (omega : ℂ)) := h.2

end RHTower
