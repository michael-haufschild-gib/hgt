import GaloisForLFunctions.SelectiveArithmetic.APoleAtTheHeightFailsBeyondTheTrivialAperture
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# The maximizing dominated contacts at a height

For a packet with nonnegative autocorrelation, the extremal real contact
weight follows the sign of the modulation cosine. Its contact form sees
the absolute cosine, whose mean is `2/π`.
-/

open Filter Topology MeasureTheory Set
open Zeta23
open scoped ArithmeticFunction.vonMangoldt Real

noncomputable section

namespace GaloisForLFunctions.SelectiveArithmetic

open AbsoluteGeometryOfSpecZ BiScaleUncertainty

/-- The dominated system maximizing each nonnegative modulated contact. -/
def signedAlignedWeight (t : ℝ) (n : ℕ) : ℝ :=
  if 0 ≤ Real.cos (t * Real.log n) then Λ n else -Λ n

theorem dominated_signedAlignedWeight (t : ℝ) : Dominated (signedAlignedWeight t) := by
  intro n
  unfold signedAlignedWeight
  split_ifs <;> simp only [abs_neg, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, le_refl]

theorem signedAlignedWeight_mul_cos (t : ℝ) (n : ℕ) :
    signedAlignedWeight t n * Real.cos (t * Real.log n) =
      Λ n * |Real.cos (t * Real.log n)| := by
  unfold signedAlignedWeight
  split_ifs with h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg (lt_of_not_ge h)]
    ring

/-- The extremal contact form is the weighted absolute-cosine sum. -/
theorem contactForm_signedAligned (t : ℝ) (f : ℝ → ℝ) (N : ℕ) :
    contactForm (signedAlignedWeight t) (_root_.RHTower.modulatedTest t f) N =
      ∑ n ∈ Finset.Icc 2 N, (Λ n : ℝ) / Real.sqrt n *
        (2 * packetAutocorr f (Real.log n)) * |Real.cos (t * Real.log n)| := by
  rw [contactForm_modulatedTest]
  apply Finset.sum_congr rfl
  intro n _
  calc
    _ = (signedAlignedWeight t n * Real.cos (t * Real.log n)) /
        Real.sqrt n * (2 * packetAutocorr f (Real.log n)) := by ring
    _ = _ := by rw [signedAlignedWeight_mul_cos]; ring

/-- Every dominated real system is bounded by the signed system on packets
with nonnegative autocorrelation. -/
theorem contactForm_le_signedAligned {w : ℕ → ℝ} (hw : Dominated w)
    {f : ℝ → ℝ} (hf : ∀ x, 0 ≤ packetAutocorr f x) (t : ℝ) (N : ℕ) :
    contactForm w (_root_.RHTower.modulatedTest t f) N ≤
      contactForm (signedAlignedWeight t) (_root_.RHTower.modulatedTest t f) N := by
  rw [contactForm_modulatedTest, contactForm_signedAligned]
  apply Finset.sum_le_sum
  intro n _
  have hn : w n * Real.cos (t * Real.log n) ≤ Λ n * |Real.cos (t * Real.log n)| := by
    calc
      _ ≤ |w n * Real.cos (t * Real.log n)| := le_abs_self _
      _ = |w n| * |Real.cos (t * Real.log n)| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right (hw n) (abs_nonneg _)
  have hh := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right hn (Real.sqrt_nonneg n))
    (mul_nonneg zero_le_two (hf (Real.log n)))
  convert hh using 1 <;> ring

private theorem abs_cos_periodic : Function.Periodic (fun x : ℝ => |Real.cos x|) π := by
  intro x
  change |Real.cos (x + π)| = |Real.cos x|
  rw [Real.cos_add_pi, abs_neg]

private theorem integral_abs_cos_period (a : ℝ) :
    (∫ x in a..a + π, |Real.cos x|) = 2 := by
  rw [abs_cos_periodic.intervalIntegral_add_eq a (-(π / 2)),
    show -(π / 2) + π = π / 2 by ring]
  have he : (∫ x in -(π / 2)..π / 2, |Real.cos x|) =
      ∫ x in -(π / 2)..π / 2, Real.cos x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by linarith only [Real.pi_pos])] at hx
    exact abs_of_nonneg (Real.cos_nonneg_of_mem_Icc hx)
  rw [he, integral_cos, Real.sin_pi_div_two, Real.sin_neg]
  norm_num

/-- Keeping all full periods loses less than two units of absolute-cosine mass. -/
theorem integral_abs_cos_ge {a b : ℝ} (hab : a ≤ b) :
    (2 / π) * (b - a) - 2 ≤ ∫ x in a..b, |Real.cos x| := by
  let n : ℕ := ⌊(b - a) / π⌋₊
  have hn : (n : ℝ) * π ≤ b - a := by
    have hh := Nat.floor_le (div_nonneg (sub_nonneg.mpr hab) Real.pi_pos.le)
    exact (le_div_iff₀ Real.pi_pos).mp hh
  have hnear : (b - a) / π < (n : ℝ) + 1 := Nat.lt_floor_add_one _
  have hi (u v : ℝ) : IntervalIntegrable (fun x : ℝ => |Real.cos x|) volume u v :=
    Real.continuous_cos.abs.intervalIntegrable _ _
  have hperiod : (∫ x in a..a + (n : ℝ) * π, |Real.cos x|) = 2 * n := by
    have hh := abs_cos_periodic.intervalIntegral_add_zsmul_eq (n : ℤ) a hi
    rw [integral_abs_cos_period] at hh
    simpa only [zsmul_eq_mul, Int.cast_natCast, mul_comm] using hh
  have hrest : 0 ≤ ∫ x in a + (n : ℝ) * π..b, |Real.cos x| :=
    intervalIntegral.integral_nonneg_of_forall (by linarith only [hn]) (fun x => abs_nonneg _)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hi a (a + (n : ℝ) * π)) (hi (a + (n : ℝ) * π) b)
  rw [hperiod] at hsplit
  have hm := (div_lt_iff₀ Real.pi_pos).mp hnear
  have hbound : (2 / π) * (b - a) - 2 ≤ 2 * n := by
    apply (le_of_lt ?_)
    rw [sub_lt_iff_lt_add, div_mul_eq_mul_div, div_lt_iff₀ Real.pi_pos]
    nlinarith only [hm]
  linarith only [hbound, hrest, hsplit]

/-- The dyadic absolute-cosine mean has the uniform error `4` at frequencies at least `1/2`. -/
theorem integral_abs_cos_mul_ge {x T : ℝ} (hx : 1 / 2 ≤ x) (hT : 0 ≤ T) :
    (2 / π) * T - 4 ≤ ∫ t in T..2 * T, |Real.cos (t * x)| := by
  have hx0 : 0 < x := by linarith only [hx]
  rw [intervalIntegral.integral_comp_mul_right (fun y => |Real.cos y|) hx0.ne', smul_eq_mul]
  have hh := mul_le_mul_of_nonneg_left
    (integral_abs_cos_ge (a := T * x) (b := 2 * T * x) (by nlinarith only [hT, hx0]))
    (inv_nonneg.mpr hx0.le)
  have hinv : x⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ hx0 (by norm_num)]
    linarith only [hx]
  have he : x⁻¹ * ((2 / π) * (2 * T * x - T * x) - 2) =
      (2 / π) * T - 2 * x⁻¹ := by
    field_simp
    <;> ring
  rw [he] at hh
  linarith only [hh, hinv]

/-- Some height in every dyadic window retains `2/π−4/T` of every nonnegative contact sum. -/
theorem exists_height_sum_abs_cos_ge (s : Finset ℕ) (c : ℕ → ℝ)
    (hc : ∀ n ∈ s, 0 ≤ c n) (hs : ∀ n ∈ s, 2 ≤ n) {T : ℝ} (hT : 0 < T) :
    ∃ t ∈ Icc T (2 * T), (2 / π - 4 / T) * ∑ n ∈ s, c n ≤
      ∑ n ∈ s, c n * |Real.cos (t * Real.log n)| := by
  have hGc : Continuous (fun t : ℝ => ∑ n ∈ s, c n * |Real.cos (t * Real.log n)|) := by
    fun_prop
  have hmean : ((2 / π) * T - 4) * ∑ n ∈ s, c n ≤
      ∫ t in T..2 * T, ∑ n ∈ s, c n * |Real.cos (t * Real.log n)| := by
    rw [intervalIntegral.integral_finsetSum
      (fun n _ => (by fun_prop : Continuous (fun t : ℝ => c n * |Real.cos (t * Real.log n)|)).intervalIntegrable _ _),
      Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    rw [intervalIntegral.integral_const_mul]
    have hlog : 1 / 2 ≤ Real.log n := by
      have hh := Real.log_two_gt_d9
      have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
        (show (2 : ℝ) ≤ n by exact_mod_cast hs n hn)
      linarith only [hh, hl]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (integral_abs_cos_mul_ge hlog hT.le) (hc n hn)
  have hTle : T ≤ 2 * T := by linarith only [hT]
  obtain ⟨t, ht, hm⟩ := (isCompact_Icc (a := T) (b := 2 * T)).exists_isMaxOn
    ⟨T, left_mem_Icc.mpr hTle⟩ hGc.continuousOn
  refine ⟨t, ht, ?_⟩
  have hup := intervalIntegral.integral_mono_on (μ := volume) hTle
    (hGc.intervalIntegrable T (2 * T)) (intervalIntegrable_const
      (c := ∑ n ∈ s, c n * |Real.cos (t * Real.log n)|))
    (fun u hu => isMaxOn_iff.mp hm u hu)
  rw [intervalIntegral.integral_const, smul_eq_mul] at hup
  have he : T * ((2 / π - 4 / T) * ∑ n ∈ s, c n) =
      ((2 / π) * T - 4) * ∑ n ∈ s, c n := by
    field_simp
    <;> ring
  apply le_of_mul_le_mul_left (a := T) ?_ hT
  rw [he]
  exact hmean.trans (hup.trans_eq (by ring))

theorem exists_height_contactForm_signedAligned_ge {f : ℝ → ℝ}
    (hf : ∀ y, 0 ≤ packetAutocorr f y) (N : ℕ) {T : ℝ} (hT : 0 < T) :
    ∃ t ∈ Icc T (2 * T),
      (2 / π - 4 / T) * contactForm (fun n => Λ n) (fun u => (f u : ℂ)) N ≤
        contactForm (signedAlignedWeight t) (_root_.RHTower.modulatedTest t f) N := by
  obtain ⟨t, ht, hh⟩ := exists_height_sum_abs_cos_ge (Finset.Icc 2 N)
    (fun n => (Λ n : ℝ) / Real.sqrt n * (2 * packetAutocorr f (Real.log n)))
    (fun n _ => mul_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg
      (Real.sqrt_nonneg _)) (mul_nonneg zero_le_two (hf _)))
    (fun n hn => (Finset.mem_Icc.mp hn).1) hT
  refine ⟨t, ht, ?_⟩
  rwa [contactForm_packet, contactForm_signedAligned]

/-- Every retained contact fraction below `2/π` gives its corresponding
additive aperture bound for the signed system. -/
theorem exists_signedAligned_height_neg {ρ η C : ℝ} (hρ : 0 < ρ)
    (hρπ : ρ < 2 / π) (hη : 0 < η) (hC : 0 ≤ C) :
    ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ a : ℝ,
      Real.log (Real.log T) - Real.log ρ + η ≤ a → Real.exp a ≤ T →
      ∃ t ∈ Icc T (2 * T),
        (_root_.RHTower.weilFullFunctional (signedAlignedWeight t)
          (EF.weilTest (_root_.RHTower.modulatedTest t (evenPolar a (η / 8)))
            (_root_.RHTower.modulatedTest t (evenPolar a (η / 8))))).re <
          -(C * ∫ u, deriv (evenPolar a (η / 8)) u ^ 2) := by
  obtain ⟨S, -, hS⟩ := exists_abs_deriv_smoothTransition_le
  let δ := η / 8
  let K := (1 / 2 + 2 * S / δ) ^ 2
  let K' := Real.log 4 + (5 + C) * K
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hK : 0 ≤ K := sq_nonneg _
  have hK' : 0 ≤ K' := by
    have hl : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    dsimp only [K']
    positivity
  have hρ1 : ρ ≤ 1 := hρπ.le.trans ((div_le_one Real.pi_pos).mpr (by linarith only [Real.pi_gt_three]))
  have hη' : 0 < 1 - Real.exp (-η / 4) := by
    have hh := Real.exp_lt_one_iff.mpr (by linarith only [hη] : -η / 4 < 0)
    linarith only [hh]
  obtain ⟨Y₀, hY₀1, hY₀⟩ := exists_riesz_ge hη'
    (by linarith only [Real.exp_pos (-η / 4)] : 1 - Real.exp (-η / 4) ≤ 1)
  have hκ : 0 < (ρ * Real.exp (-η / 2) - ρ * Real.exp (-η)) / 2 := by
    have he := Real.exp_lt_exp.mpr (by linarith only [hη] : -η < -η / 2)
    have hm := mul_lt_mul_of_pos_left he hρ
    linarith only [hm]
  obtain ⟨a₁, ha₁⟩ := eventually_atTop.mp
    (eventually_cubic_lt_exp (3 / 2 * (5 + K') + 41) hκ)
  let a₀ := max (max a₁ 1) (Real.log Y₀ / 2 + δ)
  refine ⟨max (Real.exp (Real.exp a₀)) (4 / (2 / π - ρ)), ?_⟩
  intro T hT a haT haexp
  have hTe : Real.exp (Real.exp a₀) ≤ T := (le_max_left _ _).trans hT
  have hTc : 4 / (2 / π - ρ) ≤ T := (le_max_right _ _).trans hT
  have hT0 : 0 < T := (Real.exp_pos _).trans_le hTe
  have hT1 : 1 ≤ T := (Real.one_le_exp (Real.exp_pos a₀).le).trans hTe
  let x := Real.log T
  have hxge : Real.exp a₀ ≤ x := by
    have hh := Real.log_le_log (Real.exp_pos _) hTe
    simpa only [Real.log_exp] using hh
  have hx0 : 0 < x := (Real.exp_pos _).trans_le hxge
  have hlogx : a₀ ≤ Real.log x := by
    have hh := Real.log_le_log (Real.exp_pos _) hxge
    simpa only [Real.log_exp] using hh
  have hlogρ : Real.log ρ ≤ 0 := Real.log_nonpos hρ.le hρ1
  have haa₀ : a₀ ≤ a := by dsimp only [x] at hlogx; linarith only [hlogx, haT, hlogρ, hη]
  have ha1 : 1 ≤ a := ((le_max_right a₁ 1).trans (le_max_left _ _)).trans haa₀
  have ha0 : 0 ≤ a := by linarith only [ha1]
  have haY : Real.log Y₀ / 2 + δ ≤ a := (le_max_right _ _).trans haa₀
  let E := Real.exp a
  have hE : 0 < E := Real.exp_pos _
  have haE : a ≤ E := by have hh := Real.add_one_le_exp a; linarith only [hh]
  have hxE : x ≤ ρ * Real.exp (-η) * E := by
    have hh := Real.exp_le_exp.mpr
      (show Real.log x ≤ Real.log ρ - η + a by dsimp only [x]; linarith only [haT])
    rw [Real.exp_log hx0, Real.exp_add, Real.exp_sub, Real.exp_log hρ] at hh
    simpa only [E, Real.exp_neg, div_eq_mul_inv, mul_assoc] using hh
  let M := a + Real.sinh a
  have hM0 : 0 ≤ M := add_nonneg ha0 (Real.sinh_nonneg_iff.mpr ha0)
  have hME : M ≤ a + E / 2 := by
    have he := Real.exp_pos (-a)
    dsimp only [M, E]
    rw [Real.sinh_eq]
    linarith only [he]
  have hY : Y₀ ≤ Real.exp (2 * a - 2 * δ) := by
    rw [← Real.exp_log (by linarith only [hY₀1] : 0 < Y₀)]
    exact Real.exp_le_exp.mpr (by linarith only [haY])
  have hriesz := hY₀ _ hY
  have he : (1 - (1 - Real.exp (-η / 4))) * Real.exp (2 * a - 2 * δ) =
      Real.exp (-η / 2) * E ^ 2 := by
    dsimp only [δ, E]
    rw [sub_sub_cancel, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [he] at hriesz
  have hCE := (mul_le_mul_of_nonneg_left hriesz (by norm_num : (0 : ℝ) ≤ 1 / 2)).trans
    (contactForm_evenPolar_ge (a := a) hδ)
  obtain ⟨t, ht, hmean⟩ := exists_height_contactForm_signedAligned_ge
    (packetAutocorr_evenPolar_nonneg a δ) ⌊Real.exp (2 * a)⌋₊ hT0
  refine ⟨t, ht, ?_⟩
  have ht0 : 0 < t := hT0.trans_le ht.1
  have htabs : |t| = t := abs_of_pos ht0
  have hρmean : ρ ≤ 2 / π - 4 / T := by
    have hh := (div_le_iff₀ (sub_pos.mpr hρπ)).mp hTc
    have hd : 4 / T ≤ 2 / π - ρ := (div_le_iff₀ hT0).mpr (by nlinarith only [hh])
    linarith only [hd]
  have hcontact : (ρ * Real.exp (-η / 2)) / 2 * E ^ 2 ≤
      contactForm (signedAlignedWeight t) (_root_.RHTower.modulatedTest t (evenPolar a δ))
        ⌊Real.exp (2 * a)⌋₊ := by
    apply le_trans _ hmean
    have hh := mul_le_mul hρmean hCE (by positivity) (hρ.le.trans hρmean)
    convert hh using 1 <;> ring
  have htE : Real.exp a ≤ |t| := by rw [htabs]; exact haexp.trans ht.1
  have hup := re_weilFullFunctional_modulated_le ha0 (contDiff_evenPolar a δ)
    (fun u hu => evenPolar_eq_zero hδ hu) (signedAlignedWeight t) htE
  have hlogt : Real.log (2 + |t|) ≤ x + Real.log 4 := by
    rw [htabs, ← Real.log_mul hT0.ne' (by norm_num)]
    exact Real.log_le_log (by linarith only [ht0]) (by linarith only [ht.2, hT1])
  have hκ₂ : ρ * Real.exp (-η) ≤ 1 := by
    have he : Real.exp (-η) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith only [hη])
    exact (mul_le_mul hρ1 he (Real.exp_pos _).le zero_le_one).trans_eq (by ring)
  have hbal := polar_balance ha1 hE haE hxE (by positivity) hκ₂ hM0 hME hK'
    (ha₁ a (((le_max_left a₁ 1).trans (le_max_left _ _)).trans haa₀))
  have hm := integral_evenPolar_sq_le ha0 hδ
  have hd := integral_deriv_evenPolar_sq_le hS ha0 hδ
  change _ ≤ M at hm
  change _ ≤ K * M at hd
  have hL0 : 0 ≤ Real.log (2 + |t|) + 5 := by
    have hh := Real.log_nonneg (by linarith only [abs_nonneg t] : (1 : ℝ) ≤ 2 + |t|)
    linarith only [hh]
  have hm₁ := mul_le_mul_of_nonneg_left hm hL0
  have hm₂ := mul_le_mul_of_nonneg_right hlogt hM0
  have hd₁ := mul_le_mul_of_nonneg_left hd (by linarith only [hC] : (0 : ℝ) ≤ 5 + C)
  have hpos₁ : 0 ≤ 4 * a * E * (2 + 2 * a) ^ 2 := by positivity
  have hpos₂ : 0 ≤ 4 * (2 + 2 * a) ^ 2 * M := by positivity
  dsimp only [K'] at hbal
  dsimp only [δ] at hup hcontact hm₁ hd₁
  nlinarith only [hup, hcontact, hbal, hm₁, hm₂, hd₁, hpos₁, hpos₂]

/-- The absolute-cosine mean improves the additive height-aperture upper
bound from `log 2` to `log(π/2)`. -/
theorem exists_signedAligned_height_neg_pi {η C : ℝ} (hη : 0 < η) (hC : 0 ≤ C) :
    ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ a : ℝ,
      Real.log (Real.log T) + Real.log (π / 2) + η ≤ a → Real.exp a ≤ T →
      ∃ t ∈ Icc T (2 * T),
        (_root_.RHTower.weilFullFunctional (signedAlignedWeight t)
          (EF.weilTest (_root_.RHTower.modulatedTest t (evenPolar a (η / 16)))
            (_root_.RHTower.modulatedTest t (evenPolar a (η / 16))))).re <
          -(C * ∫ u, deriv (evenPolar a (η / 16)) u ^ 2) := by
  let ρ := (2 / π) * Real.exp (-η / 2)
  have hρ : 0 < ρ := by dsimp only [ρ]; positivity
  have hρπ : ρ < 2 / π := by
    have he := Real.exp_lt_one_iff.mpr (by linarith only [hη] : -η / 2 < 0)
    simpa only [mul_one] using mul_lt_mul_of_pos_left he
      (by positivity : (0 : ℝ) < 2 / π)
  have hlog : -Real.log ρ + η / 2 = Real.log (π / 2) + η := by
    dsimp only [ρ]
    rw [Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_exp,
      Real.log_div (by norm_num) Real.pi_pos.ne',
      Real.log_div Real.pi_pos.ne' (by norm_num)]
    ring
  obtain ⟨T₀, hT₀⟩ := exists_signedAligned_height_neg hρ hρπ (half_pos hη) hC
  refine ⟨T₀, fun T hT a ha he => ?_⟩
  have ha' : Real.log (Real.log T) - Real.log ρ + η / 2 ≤ a := by
    linarith only [ha, hlog]
  simpa only [show η / 2 / 8 = η / 16 by ring] using hT₀ T hT a ha' he

/-- At arbitrarily late dyadic heights a dominated real system fails on a
packet of aperture `log log t + log(π/2) + η`. -/
theorem exists_dominated_height_neg_pi {η : ℝ} (hη : 0 < η) :
    ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∃ t ∈ Icc T (2 * T), ∃ w : ℕ → ℝ, Dominated w ∧
      ∃ f : ℝ → ℝ, ContDiff ℝ 3 f ∧
        (∀ u, Real.log (Real.log t) + Real.log (π / 2) + η ≤ |u| → f u = 0) ∧
        (_root_.RHTower.weilFullFunctional w
          (EF.weilTest (_root_.RHTower.modulatedTest t f)
            (_root_.RHTower.modulatedTest t f))).re < 0 := by
  obtain ⟨T₁, hT₁⟩ := exists_signedAligned_height_neg_pi hη (le_refl (0 : ℝ))
  have hc : 0 < 1 / ((π / 2) * Real.exp η) := by positivity
  obtain ⟨T₂, hT₂⟩ := eventually_atTop.mp (Real.isLittleO_log_id_atTop.def hc)
  refine ⟨max (max T₁ T₂) (Real.exp 1), fun T hT => ?_⟩
  have hTe : Real.exp 1 ≤ T := (le_max_right _ _).trans hT
  have hT0 : 0 < T := (Real.exp_pos _).trans_le hTe
  have hx1 : 1 ≤ Real.log T := by
    have hh := Real.log_le_log (Real.exp_pos 1) hTe
    simpa only [Real.log_exp] using hh
  have hx0 : 0 < Real.log T := zero_lt_one.trans_le hx1
  let a := Real.log (Real.log T) + Real.log (π / 2) + η
  have he : Real.exp a = ((π / 2) * Real.exp η) * Real.log T := by
    dsimp only [a]
    rw [Real.exp_add, Real.exp_add, Real.exp_log hx0,
      Real.exp_log (by positivity : (0 : ℝ) < π / 2)]
    ring
  have hlog : Real.log T ≤ 1 / ((π / 2) * Real.exp η) * T := by
    have hh := hT₂ T (((le_max_right _ _).trans (le_max_left _ _)).trans hT)
    simpa only [id_eq, Real.norm_eq_abs, abs_of_pos hx0, abs_of_pos hT0] using hh
  have haT : Real.exp a ≤ T := by
    rw [he]
    have hh := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ (π / 2) * Real.exp η)
    simpa only [← mul_assoc, mul_one_div_cancel (by positivity : (π / 2) * Real.exp η ≠ 0),
      one_mul] using hh
  obtain ⟨t, ht, hneg⟩ := hT₁ T
    (((le_max_left _ _).trans (le_max_left _ _)).trans hT) a le_rfl haT
  refine ⟨t, ht, signedAlignedWeight t, dominated_signedAlignedWeight t,
    evenPolar a (η / 16), contDiff_evenPolar _ _, ?_, ?_⟩
  · intro u hu
    have hlogt := Real.log_le_log hT0 ht.1
    have hloglog := Real.log_le_log hx0 hlogt
    apply evenPolar_eq_zero (by positivity : 0 < η / 16)
    dsimp only [a]
    linarith only [hu, hloglog]
  · simpa only [zero_mul, neg_zero] using hneg

end GaloisForLFunctions.SelectiveArithmetic
