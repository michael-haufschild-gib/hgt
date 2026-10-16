import GaloisForLFunctions.RHTower.SquareRootNevanlinnaTransfer
import GaloisForLFunctions.RHTower.OddWeilPickContinuation
import GaloisForLFunctions.RHTower.WeilConeUniquenessUnconditional

/-!
# The odd Weil cone through the square-root Herglotz transfer

For odd Weil-positive weights `lam` the slit continuation `Ψ` of the Weil function satisfies the
squared-variable sign law `Im s · Im((s − ½)Ψ(s)) ≥ 0`.

* `exists_nevanlinna_measure_of_weilPositiveOdd` (unconditional).  There are a finite circle
  measure `ν` and a real `c` with
  `a Ψ(½ + a) = ∫ i K(½ − i a², ζ) dν(ζ) − c` on the first quadrant,
  and `ν` gives no mass to the circle points `ζ ≠ 1` of ordinate `γ < −¼`: the Nevanlinna measure
  of the squared-variable Weil function lives on the critical ordinates `γ ≥ 0`, the real cut
  `−¼ ≤ γ < 0`, and the point `ζ = 1`.
* `re_nonneg_of_weilPositiveOdd_of_extension`.  If the Weil function extends holomorphically to
  all of `Re s > ½` and is nonnegative on the real half-line `s > ½`, the extension is Herglotz:
  `Re Ψ ≥ 0` on `Re s > ½`.
* `eq_vonMangoldt_and_riemannHypothesis_of_weilPositiveOdd_of_extension`.  Under the same two
  conditions `lam = Λ` on `n ≥ 2` and the Riemann hypothesis holds, through the Herglotz bridge
  `weilPositiveFull_of_herglotz` and the full-cone uniqueness theorem.  Equivalently
  (`exists_re_neg_of_weilPositiveOdd_of_ne_vonMangoldt`): every odd Weil-positive weight other
  than `Λ` has a Weil function that either does not extend across the real cut or takes a
  negative value on the real half-line.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ComplexConjugate
open Zeta23 GaloisForLFunctions.HTGeometry

noncomputable section
namespace RHTower.OddResolvent
open WeilHerglotz RHTower.AtomDomination

theorem isOpen_oddWeilSlitDomain : IsOpen oddWeilSlitDomain :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    ((isOpen_ne_fun Complex.continuous_im continuous_const).union
      (isOpen_lt continuous_const Complex.continuous_re))

/-- The Weil function is real on the real axis `s > 1`. -/
theorem weilFunction_ofReal_im (lam : ℕ → ℝ) (x : ℝ) : (weilFunction lam x).im = 0 := by
  have h := WeilSpectral.weilFunction_conj lam x
  rw [Complex.conj_ofReal] at h
  have := congrArg Complex.im h
  rw [Complex.conj_im] at this
  linarith

/-- **The Nevanlinna measure of the odd Weil function.**  For odd Weil-positive `lam` the slit
continuation `Ψ` satisfies `a Ψ(½ + a) = ∫ i K(½ − ia², ζ) dν(ζ) − c` on the first quadrant for a
finite circle measure `ν` with no mass on the ordinates `γ < −¼` (off `ζ = 1`). -/
theorem exists_nevanlinna_measure_of_weilPositiveOdd {lam : ℕ → ℝ} (hW : WeilPositiveOdd lam) :
    ∃ Ψ : ℂ → ℂ, DifferentiableOn ℂ Ψ oddWeilSlitDomain ∧
      (∀ s : ℂ, 1 < s.re → Ψ s = weilFunction lam s) ∧
      (∀ s : ℂ, 1 / 2 < s.re → s.im ≠ 0 → 0 ≤ s.im * (((s - 1 / 2) * Ψ s).im)) ∧
      ∃ ν : Measure ℝ, IsFiniteMeasure ν ∧ ∃ c : ℝ,
        ν {θ | circleMap 0 1 θ ≠ 1 ∧ angleOrd θ ∈ Iio (-(1 / 4 : ℝ))} = 0 ∧
        ∀ a : ℂ, 0 < a.re → 0 < a.im →
          a * Ψ (1 / 2 + a) =
            (∫ θ, I * hrKernel (1 / 2 - I * a ^ 2) (circleMap 0 1 θ) ∂ν) - c := by
  obtain ⟨Ψ, hΨd, hΨe, hΨs⟩ := exists_weilFunction_slit_continuation hW
  refine ⟨Ψ, hΨd, hΨe, hΨs, ?_⟩
  set F : ℂ → ℂ := fun a => Ψ (1 / 2 + a) with hF
  set D : Set ℂ := {a : ℂ | 1 / 2 + a ∈ oddWeilSlitDomain} with hD
  have hDo : IsOpen D := isOpen_oddWeilSlitDomain.preimage (by fun_prop)
  have hFd : DifferentiableOn ℂ F D := by
    intro a ha
    exact ((hΨd.differentiableAt (isOpen_oddWeilSlitDomain.mem_nhds ha)).comp a
      (by fun_prop)).differentiableWithinAt
  have hQD : {a : ℂ | 0 < a.re ∧ 0 < a.im} ⊆ D := by
    intro a ha
    show 1 / 2 + a ∈ oddWeilSlitDomain
    refine ⟨?_, Or.inl ?_⟩
    · simp only [Complex.add_re]; norm_num; linarith [ha.1]
    · simp only [Complex.add_im]; norm_num; exact ha.2.ne'
  have hFQ : DifferentiableOn ℂ F {a : ℂ | 0 < a.re ∧ 0 < a.im} := hFd.mono hQD
  have hsign : ∀ a : ℂ, 0 < a.re → 0 < a.im → 0 ≤ (a * F a).im := by
    intro a ha hai
    have h := hΨs (1 / 2 + a) (by simp; linarith) (by simp; exact hai.ne')
    have e : (1 / 2 + a - 1 / 2 : ℂ) = a := by ring
    rw [e] at h
    have hi : (1 / 2 + a : ℂ).im = a.im := by simp
    rw [hi] at h
    exact (mul_nonneg_iff_of_pos_left hai).mp h
  obtain ⟨ν, hfin, hpois, c, hrep⟩ :=
    exists_hrKernel_representation (differentiableOn_oddChart hFQ) (re_oddChart_nonneg hsign)
  refine ⟨ν, hfin, c, ?_, ?_⟩
  · -- support: no mass below the ordinate `−¼`
    refine measure_ordinate_open_eq_zero_of_poisson hpois isOpen_Iio fun t ht => ?_
    have ht' : 1 / 4 < -t := by
      have : t < -(1 / 4) := ht
      linarith
    have hx : 0 < -t := by linarith
    have hz : zPt ((1 / 2 : ℂ) + t * I) = ((-t : ℝ) : ℂ) := by
      unfold zPt
      push_cast
      ring_nf
      rw [I_sq]
      ring
    have hsq : sqrtQ ((-t : ℝ) : ℂ) = (Real.sqrt (-t) : ℂ) := sqrtQ_ofReal hx.le
    have hsqrt_gt : 1 / 2 < Real.sqrt (-t) := by
      rw [show (1 / 2 : ℝ) = Real.sqrt (1 / 4) by
        rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_lt_sqrt (by norm_num) ht'
    have hmem : sqrtQ ((-t : ℝ) : ℂ) ∈ D := by
      rw [hsq]
      show 1 / 2 + (Real.sqrt (-t) : ℂ) ∈ oddWeilSlitDomain
      refine ⟨?_, Or.inr ?_⟩
      · simp only [Complex.add_re, Complex.ofReal_re]; norm_num; linarith
      · simp only [Complex.add_re, Complex.ofReal_re]; norm_num; linarith
    have hgcont : ContinuousAt (sqNev F) ((-t : ℝ) : ℂ) :=
      (differentiableAt_sqNev hDo hFd (mem_slitPlane_of_re_pos (by simpa using hx))
        hmem).continuousAt
    have hgreal : (sqNev F ((-t : ℝ) : ℂ)).im = 0 := by
      unfold sqNev
      rw [hsq, Complex.im_ofReal_mul]
      have hre1 : 1 < ((1 / 2 : ℂ) + (Real.sqrt (-t) : ℂ)).re := by
        simp only [Complex.add_re, Complex.ofReal_re]; norm_num; linarith
      have hval : F (Real.sqrt (-t) : ℂ) = weilFunction lam (((1 / 2 + Real.sqrt (-t) : ℝ)) : ℂ) := by
        simp only [hF]
        rw [hΨe _ hre1]
        push_cast
        rfl
      rw [hval, weilFunction_ofReal_im, mul_zero]
    have hcont : ContinuousAt (fun s => (oddChart F s).re) ((1 / 2 : ℂ) + t * I) := by
      simp only [re_oddChart]
      have hg : ContinuousAt (sqNev F) (zPt ((1 / 2 : ℂ) + t * I)) := by
        rw [hz]
        exact hgcont
      exact Complex.continuous_im.continuousAt.comp
        (hg.comp differentiable_zPt.continuous.continuousAt)
    have hval : (oddChart F ((1 / 2 : ℂ) + t * I)).re = 0 := by
      rw [re_oddChart, hz]
      exact hgreal
    rw [← hval]
    exact hcont.tendsto.mono_left nhdsWithin_le_nhds
  · -- the interior representation
    intro a ha hai
    have hs : 1 / 2 < (1 / 2 - I * a ^ 2).re := by
      rw [re_half_sub_I_mul]
      have : 0 < (a ^ 2).im := by simp [pow_two, Complex.mul_im]; positivity
      linarith
    have h := hrep _ hs
    rw [oddChart, zPt_half_sub, sqNev_sq ha] at h
    rw [integral_const_mul]
    have e : a * Ψ (1 / 2 + a) = I * (-I * (a * F a)) := by
      simp only [hF]; ring_nf; rw [I_sq]; ring
    rw [e, h]
    ring_nf
    rw [I_sq]
    ring

/-- **Odd positivity, a cut-free extension and real nonnegativity give the Herglotz property.**
If the Weil function of an odd Weil-positive `lam` extends holomorphically to `Re s > ½` and the
extension is nonnegative on the real half-line `s > ½`, then `Re Ψ ≥ 0` on `Re s > ½`. -/
theorem re_nonneg_of_weilPositiveOdd_of_extension {lam : ℕ → ℝ} (hW : WeilPositiveOdd lam)
    {Ψ : ℂ → ℂ} (hΨd : DifferentiableOn ℂ Ψ {s : ℂ | 1 / 2 < s.re})
    (hΨe : ∀ s : ℂ, 1 < s.re → Ψ s = weilFunction lam s)
    (hpos : ∀ x : ℝ, 1 / 2 < x → 0 ≤ (Ψ x).re) :
    ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Ψ s).re := by
  have hW' := weilPositiveOddAt_one_iff.mpr hW
  set F : ℂ → ℂ := fun a => Ψ (1 / 2 + a) with hF
  have hH : IsOpen {s : ℂ | 1 / 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hFd : DifferentiableOn ℂ F {a : ℂ | 0 < a.re} := by
    intro a ha
    have hmem : (1 / 2 : ℂ) + a ∈ {s : ℂ | 1 / 2 < s.re} := by
      show 1 / 2 < ((1 / 2 : ℂ) + a).re
      simp only [Complex.add_re]; norm_num; exact ha
    exact ((hΨd.differentiableAt (hH.mem_nhds hmem)).comp a (by fun_prop)).differentiableWithinAt
  have hconj : ∀ a : ℂ, 0 < a.re → F (conj a) = conj (F a) := by
    intro a ha
    simp only [hF]
    have h := herglotz_conj hΨd hΨe (s := 1 / 2 + a) (by simp; linarith)
    rw [← h]
    congr 1
    simp only [map_add, map_div₀, map_one, map_ofNat]
  have hpos' : ∀ x : ℝ, 0 < x → 0 ≤ (F x).re := by
    intro x hx
    simp only [hF]
    have h := hpos (1 / 2 + x) (by linarith)
    push_cast at h
    exact h
  -- the sign law, transported by the identity theorem on the first quadrant
  obtain ⟨F₀, hF₀d, hF₀e, hF₀p⟩ := exists_nonreal_continuation_of_weilPositiveOddAt hW'
  have hsign : ∀ a : ℂ, 0 < a.re → 0 < a.im → 0 ≤ (a * F a).im := by
    have hQ : IsOpen {a : ℂ | 0 < a.re ∧ 0 < a.im} :=
      (isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt continuous_const Complex.continuous_im)
    have hQc : IsPreconnected {a : ℂ | 0 < a.re ∧ 0 < a.im} :=
      ((convex_halfSpace_re_gt 0).inter (convex_halfSpace_im_gt 0)).isPreconnected
    have hFQ : DifferentiableOn ℂ F {a : ℂ | 0 < a.re ∧ 0 < a.im} := hFd.mono fun a ha => ha.1
    have hF₀Q : DifferentiableOn ℂ F₀ {a : ℂ | 0 < a.re ∧ 0 < a.im} :=
      hF₀d.mono fun a ha => ⟨ha.1, ha.2.ne'⟩
    have heq : F =ᶠ[𝓝 (1 + I : ℂ)] F₀ := by
      have hm : {a : ℂ | 1 / 2 < a.re ∧ 0 < a.im} ∈ 𝓝 (1 + I : ℂ) :=
        ((isOpen_lt continuous_const Complex.continuous_re).inter
          (isOpen_lt continuous_const Complex.continuous_im)).mem_nhds (by norm_num)
      filter_upwards [hm] with a ha
      simp only [hF]
      rw [hΨe _ (by simp; linarith [ha.1]), hF₀e a ha.1 ha.2.ne', add_comm]
    have hEq := (hFQ.analyticOnNhd hQ).eqOn_of_preconnected_of_eventuallyEq
      (hF₀Q.analyticOnNhd hQ) hQc (show (1 + I : ℂ) ∈ {a : ℂ | 0 < a.re ∧ 0 < a.im} by norm_num)
      heq
    intro a ha hai
    rw [hEq ⟨ha, hai⟩]
    exact (mul_nonneg_iff_of_pos_left hai).mp (hF₀p a ha hai.ne')
  have hmain := re_nonneg_of_sqrt_sign_law hFd hsign hconj hpos'
  intro s hs
  have h := hmain (s - 1 / 2) (by simp; linarith)
  simp only [hF, add_sub_cancel] at h
  exact h

/-- **Odd positivity, a cut-free extension and real nonnegativity force `Λ` and RH.** -/
theorem eq_vonMangoldt_and_riemannHypothesis_of_weilPositiveOdd_of_extension {lam : ℕ → ℝ}
    (hW : WeilPositiveOdd lam) {Ψ : ℂ → ℂ}
    (hΨd : DifferentiableOn ℂ Ψ {s : ℂ | 1 / 2 < s.re})
    (hΨe : ∀ s : ℂ, 1 < s.re → Ψ s = weilFunction lam s)
    (hpos : ∀ x : ℝ, 1 / 2 < x → 0 ≤ (Ψ x).re) :
    (∀ n, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis := by
  have hW' := weilPositiveOddAt_one_iff.mpr hW
  have hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ := fun σ hσ =>
    OddSector.summable_abs_div_rpow_of_weilPositiveOddAt_anyWeight hW' hσ
  have hre := re_nonneg_of_weilPositiveOdd_of_extension hW hΨd hΨe hpos
  have hfull : WeilPositiveFull lam := weilPositiveFull_of_herglotz hsl hΨd hre hΨe
  have h := WeilSpectral.weilPositiveFull_iff_riemannHypothesis_and_eq_vonMangoldt.mp hfull
  exact ⟨h.2, h.1⟩

/-- **Classification of odd fakes.**  An odd Weil-positive weight other than `Λ` has a Weil
function that, whenever it extends holomorphically to `Re s > ½`, is negative somewhere on the
real half-line `s > ½`. -/
theorem exists_re_neg_of_weilPositiveOdd_of_ne_vonMangoldt {lam : ℕ → ℝ}
    (hW : WeilPositiveOdd lam) (hne : ¬ ∀ n, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n)
    {Ψ : ℂ → ℂ} (hΨd : DifferentiableOn ℂ Ψ {s : ℂ | 1 / 2 < s.re})
    (hΨe : ∀ s : ℂ, 1 < s.re → Ψ s = weilFunction lam s) :
    ∃ x : ℝ, 1 / 2 < x ∧ (Ψ x).re < 0 := by
  by_contra h
  push Not at h
  exact hne (eq_vonMangoldt_and_riemannHypothesis_of_weilPositiveOdd_of_extension hW hΨd hΨe
    fun x hx => h x hx).1

end RHTower.OddResolvent
