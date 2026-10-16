import GaloisForLFunctions.RHTower.OddWeilResolventArithmetic
import GaloisForLFunctions.RHTower.OddWeilGramLimit
import Mathlib.Analysis.Complex.Convex

/-!
# Automatic slit continuation from odd Weil positivity

For every `WeilPositiveOdd lam` source, its actual arithmetic Weil function
continues holomorphically to `Re s > 1/2` with only the real segment
`1/2 < s ≤ 1` omitted. It agrees with the original function throughout
`Re s > 1` and satisfies the squared-variable Pick sign law off the real axis.

The producer is the exact mixed resolvent Gram identity: compact odd
positivity makes `(a F(a) - conj (b F(b))) / (a² - conj(b)²)` positive
semidefinite, where `F(a) = weilFunction lam (a + 1/2)`. Rotating the square
by `-I` turns this into a Carathéodory interpolation kernel. Pullback,
analytic uniqueness, and conjugate reflection give the continuation.

No continuation, representing measure, or kernel positivity is assumed.
The real cut and arbitrary-weight uniqueness remain unresolved.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ComplexConjugate
open Zeta23 GaloisForLFunctions.HTGeometry

noncomputable section
namespace RHTower.OddResolvent
open WeilHerglotz

abbrev SeedWidth := {a : ℂ // 2 ≤ a.re ∧ 0 < a.im}

def oddPickKernel (lam : ℕ → ℝ) (a b : ℂ) : ℂ :=
  (a * weilFunction lam (a + 1 / 2) - conj (b * weilFunction lam (b + 1 / 2))) /
    (a ^ 2 - (conj b) ^ 2)

theorem isPSDKernel_oddPickKernel {lam : ℕ → ℝ} (hW : WeilPositiveOddAt 1 lam) :
    IsPSDKernel fun a b : SeedWidth => oddPickKernel lam a b := by
  have hM : IsPSDKernel fun a b : SeedWidth => mixedWeilLimit lam a b :=
    isPSDKernel_limit
      (fun j => isPSDKernel_weilOdd hW (fun a : SeedWidth => oddTest a j)
        (fun a => contDiff_oddTest a j) (fun a => hasCompactSupport_oddTest a j)
        (fun a x => oddTest_odd a j x))
      (fun a b => tendsto_weil_mixed hW a.2.1 b.2.1)
  refine (hM.const_mul (c := 1 / 4) (by norm_num)).congr fun a b => ?_
  rw [mixedWeilLimit_eq hW a.2.1 a.2.2 b.2.1 b.2.2]
  unfold oddPickKernel
  push_cast
  ring

theorem rotatedSquare_kernel (a b A B : ℂ) :
    ((-I * (a * A)) + conj (-I * (b * B))) /
        ((-I * a ^ 2) + conj (-I * b ^ 2)) =
      (a * A - conj (b * B)) / (a ^ 2 - (conj b) ^ 2) := by
  have hn : -I * (a * A) + conj (-I * (b * B)) = -I * (a * A - conj (b * B)) := by
    simp only [map_mul, map_neg, conj_I]
    ring
  have hd : -I * a ^ 2 + conj (-I * b ^ 2) = -I * (a ^ 2 - (conj b) ^ 2) := by
    simp only [map_mul, map_neg, conj_I, map_pow]
    ring
  rw [hn, hd, mul_div_mul_left _ _ (neg_ne_zero.mpr I_ne_zero)]

theorem rotatedSquare_re_pos {a : ℂ} (ha : 0 < a.re) (hai : 0 < a.im) :
    0 < (-I * a ^ 2).re := by
  norm_num [pow_two, Complex.mul_re, Complex.mul_im]
  nlinarith [mul_pos ha hai]

theorem exists_upper_continuation_seed {lam : ℕ → ℝ} (hW : WeilPositiveOddAt 1 lam) :
    ∃ F : ℂ → ℂ,
      DifferentiableOn ℂ F {a : ℂ | 0 < a.re ∧ 0 < a.im} ∧
      (∀ a : ℂ, 2 ≤ a.re → 0 < a.im → F a = weilFunction lam (a + 1 / 2)) ∧
      (∀ a : ℂ, 0 < a.re → 0 < a.im → 0 ≤ (a * F a).im) := by
  letI : Nonempty SeedWidth := ⟨⟨3 + I, by constructor <;> norm_num⟩⟩
  have hq : ∀ a : SeedWidth, 0 < (-I * (a : ℂ) ^ 2).re := fun a =>
    rotatedSquare_re_pos (by linarith [a.2.1]) a.2.2
  have hK : IsPSDKernel (fun a b : SeedWidth =>
      ((-I * ((a : ℂ) * weilFunction lam ((a : ℂ) + 1 / 2))) +
        conj (-I * ((b : ℂ) * weilFunction lam ((b : ℂ) + 1 / 2)))) /
      ((-I * (a : ℂ) ^ 2) + conj (-I * (b : ℂ) ^ 2))) :=
    (isPSDKernel_oddPickKernel hW).congr fun a b =>
      (rotatedSquare_kernel a b (weilFunction lam ((a : ℂ) + 1 / 2))
        (weilFunction lam ((b : ℂ) + 1 / 2))).symm
  obtain ⟨G, hGd, hGre, hGe⟩ := exists_caratheodory_interpolant
    (fun a : SeedWidth => -I * (a : ℂ) ^ 2)
    (fun a : SeedWidth => -I * ((a : ℂ) * weilFunction lam ((a : ℂ) + 1 / 2))) hq hK
  let F : ℂ → ℂ := fun a => I * G (-I * a ^ 2) / a
  refine ⟨F, ?_, ?_, ?_⟩
  · intro a ha
    have hqa := rotatedSquare_re_pos ha.1 ha.2
    have hGa := hGd.differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hqa)
    have hqd : Differentiable ℂ (fun a : ℂ => -I * a ^ 2) := by fun_prop
    have hna : a ≠ 0 := by intro h; norm_num [h] at ha
    exact (((hGa.comp a hqd.differentiableAt).const_mul I).div
      differentiableAt_id hna).differentiableWithinAt
  · intro a ha hai
    have hval := hGe ⟨a, ha, hai⟩
    change G (-I * a ^ 2) = -I * (a * weilFunction lam (a + 1 / 2)) at hval
    have hna : a ≠ 0 := by intro h; norm_num [h] at ha
    change I * G (-I * a ^ 2) / a = _
    rw [hval]
    field_simp
    ring_nf
    simp only [I_sq]
    ring
  · intro a ha hai
    have h := hGre (-I * a ^ 2) (rotatedSquare_re_pos ha hai)
    have hna : a ≠ 0 := by intro h; simp [h] at ha
    have he : a * F a = I * G (-I * a ^ 2) := by dsimp [F]; field_simp
    rw [he]
    simpa using h

theorem exists_upper_continuation {lam : ℕ → ℝ} (hW : WeilPositiveOddAt 1 lam) :
    ∃ F : ℂ → ℂ,
      DifferentiableOn ℂ F {a : ℂ | 0 < a.re ∧ 0 < a.im} ∧
      (∀ a : ℂ, 1 / 2 < a.re → 0 < a.im → F a = weilFunction lam (a + 1 / 2)) ∧
      (∀ a : ℂ, 0 < a.re → 0 < a.im → 0 ≤ (a * F a).im) := by
  obtain ⟨F, hFd, hFe, hFp⟩ := exists_upper_continuation_seed hW
  refine ⟨F, hFd, ?_, hFp⟩
  let V : Set ℂ := {a | 1 / 2 < a.re ∧ 0 < a.im}
  have hVo : IsOpen V := (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt continuous_const Complex.continuous_im)
  have hVc : IsPreconnected V :=
    ((convex_halfSpace_re_gt (1 / 2)).inter (convex_halfSpace_im_gt 0)).isPreconnected
  have hFV : DifferentiableOn ℂ F V := hFd.mono fun a ha => ⟨by linarith [ha.1], ha.2⟩
  have hsl := fun σ (hσ : 1 < σ) =>
    OddSector.summable_abs_div_rpow_of_weilPositiveOddAt_anyWeight hW hσ
  have hWV : DifferentiableOn ℂ (fun a => weilFunction lam (a + 1 / 2)) V := by
    intro a ha
    have hh := WeilPoleWeight.differentiableAt_weilFunction_of_summable hsl
      (s := a + 1 / 2) (by norm_num; linarith [ha.1])
    exact (hh.comp a (show DifferentiableAt ℂ (fun z : ℂ => z + 1 / 2) a by
      fun_prop)).differentiableWithinAt
  have he : F =ᶠ[𝓝 (3 + I : ℂ)] (fun a => weilFunction lam (a + 1 / 2)) := by
    have hm : {a : ℂ | 2 < a.re ∧ 0 < a.im} ∈ 𝓝 (3 + I : ℂ) :=
      ((isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt continuous_const Complex.continuous_im)).mem_nhds (by norm_num)
    filter_upwards [hm] with a ha
    exact hFe a ha.1.le ha.2
  have hEq := (hFV.analyticOnNhd hVo).eqOn_of_preconnected_of_eventuallyEq
    (hWV.analyticOnNhd hVo) hVc (show (3 + I : ℂ) ∈ V by dsimp [V]; norm_num) he
  exact fun a ha hai => hEq ⟨ha, hai⟩

theorem weilFunction_conj_width (lam : ℕ → ℝ) (a : ℂ) :
    weilFunction lam (conj a + 1 / 2) = conj (weilFunction lam (a + 1 / 2)) := by
  have he : (conj a + 1 / 2) / 2 = conj ((a + 1 / 2) / 2) := by
    simp only [map_div₀, map_add, map_one, map_ofNat]
  simp only [weilFunction]
  rw [he, Zeta23.digamma_conj, lseries_conj_width]
  simp only [map_sub, map_add, map_div₀, map_one, map_ofNat, conj_ofReal]

theorem exists_nonreal_continuation_of_weilPositiveOddAt {lam : ℕ → ℝ}
    (hW : WeilPositiveOddAt 1 lam) :
    ∃ F : ℂ → ℂ,
      DifferentiableOn ℂ F {a : ℂ | 0 < a.re ∧ a.im ≠ 0} ∧
      (∀ a : ℂ, 1 / 2 < a.re → a.im ≠ 0 → F a = weilFunction lam (a + 1 / 2)) ∧
      (∀ a : ℂ, 0 < a.re → a.im ≠ 0 → 0 ≤ a.im * (a * F a).im) := by
  obtain ⟨P, hPd, hPe, hPp⟩ := exists_upper_continuation hW
  let F : ℂ → ℂ := fun a => if 0 < a.im then P a else conj (P (conj a))
  have hUo : IsOpen {a : ℂ | 0 < a.re ∧ 0 < a.im} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hPa : ∀ a : ℂ, 0 < a.re → 0 < a.im → DifferentiableAt ℂ P a :=
    fun a ha hai => hPd.differentiableAt (hUo.mem_nhds ⟨ha, hai⟩)
  refine ⟨F, ?_, ?_, ?_⟩
  · intro a ha
    by_cases hai : 0 < a.im
    · apply DifferentiableAt.differentiableWithinAt
      apply (hPa a ha.1 hai).congr_of_eventuallyEq
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds hai] with z hz
      simp only [F, if_pos hz]
    · have hneg : a.im < 0 := lt_of_le_of_ne (le_of_not_gt hai) ha.2
      have hca := hPa (conj a) (by simpa using ha.1) (by simpa using neg_pos.mpr hneg)
      have hlow : DifferentiableAt ℂ (fun z => conj (P (conj z))) a := by
        simpa only [conj_conj, Function.comp_def] using hca.conj_conj
      apply DifferentiableAt.differentiableWithinAt
      apply hlow.congr_of_eventuallyEq
      filter_upwards [(isOpen_lt Complex.continuous_im continuous_const).mem_nhds hneg] with z hz
      simp only [F, if_neg (not_lt.mpr hz.le)]
  · intro a ha hai
    by_cases hpos : 0 < a.im
    · simp only [F, if_pos hpos]
      exact hPe a ha hpos
    · have hneg : a.im < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hai
      simp only [F, if_neg hpos]
      rw [hPe (conj a) (by simpa using ha) (by simpa using neg_pos.mpr hneg),
        weilFunction_conj_width, conj_conj]
  · intro a ha hai
    by_cases hpos : 0 < a.im
    · simp only [F, if_pos hpos]
      exact mul_nonneg hpos.le (hPp a ha hpos)
    · have hneg : a.im < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hai
      have h := hPp (conj a) (by simpa using ha) (by simpa using neg_pos.mpr hneg)
      have he : a * F a = conj ((conj a) * P (conj a)) := by
        simp only [F, if_neg hpos, map_mul, conj_conj]
      rw [he, conj_im]
      nlinarith

def oddWeilSlitDomain : Set ℂ := {s | 1 / 2 < s.re ∧ (s.im ≠ 0 ∨ 1 < s.re)}

theorem exists_weilFunction_slit_continuation {lam : ℕ → ℝ} (hW : WeilPositiveOdd lam) :
    ∃ Ψ : ℂ → ℂ,
      DifferentiableOn ℂ Ψ oddWeilSlitDomain ∧
      (∀ s : ℂ, 1 < s.re → Ψ s = weilFunction lam s) ∧
      (∀ s : ℂ, 1 / 2 < s.re → s.im ≠ 0 →
        0 ≤ s.im * (((s - 1 / 2) * Ψ s).im)) := by
  have hW' := weilPositiveOddAt_one_iff.mpr hW
  obtain ⟨F, hFd, hFe, hFp⟩ := exists_nonreal_continuation_of_weilPositiveOddAt hW'
  let U : Set ℂ := {s | 1 / 2 < s.re ∧ s.im ≠ 0}
  let A : ℂ → ℂ := fun s => F (s - 1 / 2)
  have hUo : IsOpen U := (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_ne_fun Complex.continuous_im continuous_const)
  have hAd : DifferentiableOn ℂ A U := by
    apply hFd.comp (show DifferentiableOn ℂ (fun s : ℂ => s - 1 / 2) U by fun_prop)
    intro s hs
    constructor
    · simp only [Complex.sub_re, Complex.div_ofNat_re, one_re]
      linarith [hs.1]
    · simpa using hs.2
  have hAe : ∀ s : ℂ, 1 < s.re → s.im ≠ 0 → A s = weilFunction lam s := by
    intro s hs hi
    have h := hFe (s - 1 / 2) (by norm_num; linarith) (by simpa using hi)
    simpa only [sub_add_cancel] using h
  have hAp : ∀ s : ℂ, 1 / 2 < s.re → s.im ≠ 0 →
      0 ≤ s.im * (((s - 1 / 2) * A s).im) := by
    intro s hs hi
    have h := hFp (s - 1 / 2) (by norm_num; linarith) (by simpa using hi)
    simpa only [Complex.sub_im, Complex.div_ofNat_im, one_im, zero_div, sub_zero] using h
  let Ψ : ℂ → ℂ := fun s => if 1 < s.re then weilFunction lam s else A s
  have hΨA : ∀ s : ℂ, s.im ≠ 0 → Ψ s = A s := by
    intro s hi
    dsimp [Ψ]
    split_ifs with hs
    · exact (hAe s hs hi).symm
    · rfl
  have hsl := fun σ (hσ : 1 < σ) =>
    OddSector.summable_abs_div_rpow_of_weilPositiveOddAt_anyWeight hW' hσ
  refine ⟨Ψ, ?_, ?_, ?_⟩
  · intro s hs
    by_cases hre : 1 < s.re
    · apply DifferentiableAt.differentiableWithinAt
      apply (WeilPoleWeight.differentiableAt_weilFunction_of_summable hsl hre).congr_of_eventuallyEq
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hre] with z hz
      simp only [Ψ, if_pos hz]
    · have hi : s.im ≠ 0 := hs.2.resolve_right hre
      apply DifferentiableAt.differentiableWithinAt
      apply (hAd.differentiableAt (hUo.mem_nhds ⟨hs.1, hi⟩)).congr_of_eventuallyEq
      filter_upwards [(isOpen_ne_fun Complex.continuous_im continuous_const).mem_nhds hi] with z hz
      exact hΨA z hz
  · intro s hs
    simp only [Ψ, if_pos hs]
  · intro s hs hi
    rw [hΨA s hi]
    exact hAp s hs hi

end RHTower.OddResolvent
