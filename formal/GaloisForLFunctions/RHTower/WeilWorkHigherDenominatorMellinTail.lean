import GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorMellinTailSupport
import Mathlib.Analysis.Complex.CauchyIntegral
import GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorBoundaryPrimitive

/-!
# Holomorphic smooth tails of the actual Fourier primitive

The upper tail is identified with its absolutely convergent second-derivative
integral. Its Mellin expansion is holomorphic for `re s < 2`, apart from the
constant-term endpoint at zero. The final theorem obtains every estimate from
the original cubic datum and an explicit fixed cutoff. Local regularity of the
inversion defect is not assumed or proved here.
-/

noncomputable section
open Complex MeasureTheory Set Filter Topology Asymptotics
open scoped ContDiff
namespace RHTower.WeilHigherDenominator
private lemma hasDerivAt_positive_cpow {x : ℝ} (hx : 0 < x) (s : ℂ) :
    HasDerivAt (fun y : ℝ => (y : ℂ) ^ s) (s * (x : ℂ) ^ (s - 1)) x := by
  by_cases hs : s = 0
  · subst s
    simpa using hasDerivAt_const x (1 : ℂ)
  exact hasDerivAt_ofReal_cpow_const (ne_of_gt hx) hs

theorem iteratedDeriv_two_cutoff_cpow {ψ : ℝ → ℂ} (hψ : ContDiff ℝ ∞ ψ)
    (s : ℂ) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv 2 (fun y : ℝ => ψ y * (y : ℂ) ^ (s - 1)) x =
      iteratedDeriv 2 ψ x * (x : ℂ) ^ (s - 1) +
      2 * (s - 1) * iteratedDeriv 1 ψ x * (x : ℂ) ^ (s - 2) +
      (s - 1) * (s - 2) * ψ x * (x : ℂ) ^ (s - 3) := by
  have hp (y : ℝ) (hy : 0 < y) := hasDerivAt_positive_cpow hy (s - 1)
  have hp' : HasDerivAt (fun y : ℝ => (y : ℂ) ^ (s - 1))
      ((s - 1) * (x : ℂ) ^ (s - 2)) x := by
    simpa only [show s - 1 - 1 = s - 2 by ring] using hp x hx
  have hp'' : HasDerivAt (fun y : ℝ => (y : ℂ) ^ (s - 2))
      ((s - 2) * (x : ℂ) ^ (s - 3)) x := by
    simpa only [show s - 2 - 1 = s - 3 by ring] using hasDerivAt_positive_cpow hx (s - 2)
  have hd : HasDerivAt ψ (iteratedDeriv 1 ψ x) x := by
    simpa only [iteratedDeriv_one] using (hψ.differentiable (by simp) x).hasDerivAt
  have hd' : HasDerivAt (iteratedDeriv 1 ψ) (iteratedDeriv 2 ψ x) x := by
    simpa only [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ] using
      (hψ.differentiable_iteratedDeriv 1 (by simp) x).hasDerivAt
  have he : deriv (fun y : ℝ => ψ y * (y : ℂ) ^ (s - 1)) =ᶠ[𝓝 x]
      fun y => iteratedDeriv 1 ψ y * (y : ℂ) ^ (s - 1) +
        ψ y * ((s - 1) * (y : ℂ) ^ (s - 2)) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    simpa only [Pi.mul_apply, iteratedDeriv_one, show s - 1 - 1 = s - 2 by ring] using
      ((hψ.differentiable (by simp) y).hasDerivAt.fun_mul (hp y hy)).deriv
  have hh := ((hd'.mul hp').add (hd.mul (hp''.const_mul (s - 1)))).congr_of_eventuallyEq he
  conv_lhs => rw [iteratedDeriv_succ (n := 1), iteratedDeriv_one]
  rw [hh.deriv]
  ring

/-- The expanded smooth tail of the actual second-primitive pairing. -/
def primitiveMellinTail (F : ℝ → ℂ) (A : ℂ) (ψ : ℝ → ℂ) (s : ℂ) : ℂ :=
  -(A / s) * mellin (iteratedDeriv 1 ψ) (s + 1) +
    mellin (fun x => F x * iteratedDeriv 2 ψ x) s +
    (2 * (s - 1)) * mellin (fun x => F x * iteratedDeriv 1 ψ x) (s - 1) +
    ((s - 1) * (s - 2)) * mellin (fun x => F x * ψ x) (s - 2)

theorem differentiableAt_primitiveMellinTail {ψ F : ℝ → ℂ}
    (hψ : IsMellinTailCutoff ψ) (hF : Continuous F)
    (hB : ∃ C : ℝ, ∀ x, ‖F x‖ ≤ C) (A : ℂ) {s : ℂ}
    (hs : s.re < 2) (hs0 : s ≠ 0) :
    DifferentiableAt ℂ (primitiveMellinTail F A ψ) s := by
  have h1 (z : ℂ) : DifferentiableAt ℂ (mellin (iteratedDeriv 1 ψ)) z := by
    simpa only [one_mul] using
      (hψ.mellin_mul_iteratedDeriv (F := fun _ => 1) continuous_const (by decide : 1 ≠ 0) z).2
  have h2 := (hψ.mellin_mul_iteratedDeriv hF (by decide : 2 ≠ 0) s).2
  have h3 := (hψ.mellin_mul_iteratedDeriv hF (by decide : 1 ≠ 0) (s - 1)).2
  have h4 := (hψ.mellin_mul hF hB (s := s - 2) (by simpa using hs)).2
  exact (((((differentiableAt_const A).div differentiableAt_id hs0).neg.mul
    ((h1 (s + 1)).comp s (differentiableAt_id.add_const 1))).add h2).add
      (((differentiableAt_id.sub_const 1).const_mul 2).mul
        (h3.comp s (differentiableAt_id.sub_const 1)))).add
      (((differentiableAt_id.sub_const 1).mul (differentiableAt_id.sub_const 2)).mul
        (h4.comp s (differentiableAt_id.sub_const 2)))

theorem analyticAt_primitiveMellinTail {ψ F : ℝ → ℂ}
    (hψ : IsMellinTailCutoff ψ) (hF : Continuous F)
    (hB : ∃ C : ℝ, ∀ x, ‖F x‖ ≤ C) (A : ℂ) {s : ℂ}
    (hs : s.re < 2) (hs0 : s ≠ 0) :
    AnalyticAt ℂ (primitiveMellinTail F A ψ) s := by
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  filter_upwards [(isOpen_lt Complex.continuous_re continuous_const).mem_nhds hs,
    isOpen_ne.mem_nhds hs0] with z hz hz0
  exact differentiableAt_primitiveMellinTail hψ hF hB A hz hz0

private lemma cutoff_cpow_second_integrand {ψ F : ℝ → ℂ}
    (hψ : ContDiff ℝ ∞ ψ) (s : ℂ) {x : ℝ} (hx : 0 < x) :
    F x * iteratedDeriv 2 (fun y : ℝ => ψ y * (y : ℂ) ^ (s - 1)) x =
      (x : ℂ) ^ (s - 1) * (F x * iteratedDeriv 2 ψ x) +
      (2 * (s - 1)) * ((x : ℂ) ^ (s - 1 - 1) * (F x * iteratedDeriv 1 ψ x)) +
      ((s - 1) * (s - 2)) * ((x : ℂ) ^ (s - 2 - 1) * (F x * ψ x)) := by
  rw [iteratedDeriv_two_cutoff_cpow hψ s hx]
  rw [show s - 1 - 1 = s - 2 by ring, show s - 2 - 1 = s - 3 by ring]
  ring

/-- The second-derivative integral is absolutely convergent and has the stated Mellin expansion. -/
theorem integral_primitive_cutoff_cpow {ψ F : ℝ → ℂ}
    (hψ : IsMellinTailCutoff ψ) (hF : Continuous F)
    (hB : ∃ C : ℝ, ∀ x, ‖F x‖ ≤ C) {s : ℂ} (hs : s.re < 2) :
    IntegrableOn (fun x : ℝ =>
      F x * iteratedDeriv 2 (fun y : ℝ => ψ y * (y : ℂ) ^ (s - 1)) x) (Ioi 0) ∧
    (∫ x : ℝ in Ioi 0, F x * iteratedDeriv 2 (fun y : ℝ => ψ y * (y : ℂ) ^ (s - 1)) x) =
      mellin (fun x => F x * iteratedDeriv 2 ψ x) s +
      (2 * (s - 1)) * mellin (fun x => F x * iteratedDeriv 1 ψ x) (s - 1) +
      ((s - 1) * (s - 2)) * mellin (fun x => F x * ψ x) (s - 2) := by
  have h2 := (hψ.mellin_mul_iteratedDeriv hF (by decide : 2 ≠ 0) s).1
  have h1 := (hψ.mellin_mul_iteratedDeriv hF (by decide : 1 ≠ 0) (s - 1)).1
  have h0 := (hψ.mellin_mul hF hB (s := s - 2) (by simpa using hs)).1
  simp only [MellinConvergent, smul_eq_mul] at h2 h1 h0
  have he : (fun x : ℝ => F x * iteratedDeriv 2 (fun y : ℝ => ψ y * (y : ℂ) ^ (s - 1)) x) =ᵐ[volume.restrict (Ioi 0)]
      fun x => (x : ℂ) ^ (s - 1) * (F x * iteratedDeriv 2 ψ x) +
        (2 * (s - 1)) * ((x : ℂ) ^ (s - 1 - 1) * (F x * iteratedDeriv 1 ψ x)) +
        ((s - 1) * (s - 2)) * ((x : ℂ) ^ (s - 2 - 1) * (F x * ψ x)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact cutoff_cpow_second_integrand hψ.smooth s hx
  refine ⟨((h2.add (h1.const_mul _)).add (h0.const_mul _)).congr he.symm, ?_⟩
  rw [integral_congr_ae he]
  have hi := integral_add (h2.add (h1.const_mul (2 * (s - 1))))
    (h0.const_mul ((s - 1) * (s - 2)))
  simp only [Pi.add_apply] at hi
  rw [hi, integral_add h2 (h1.const_mul (2 * (s - 1))), integral_const_mul, integral_const_mul]
  rfl

/-- The expanded transform is the actual second-primitive tail integral. -/
theorem primitiveMellinTail_eq_integral {ψ F : ℝ → ℂ}
    (hψ : IsMellinTailCutoff ψ) (hF : Continuous F)
    (hB : ∃ C : ℝ, ∀ x, ‖F x‖ ≤ C) (A : ℂ) {s : ℂ} (hs : s.re < 2) :
    primitiveMellinTail F A ψ s =
      -(A / s) * (∫ x : ℝ in Ioi 0, iteratedDeriv 1 ψ x * (x : ℂ) ^ s) +
      (∫ x : ℝ in Ioi 0, F x * iteratedDeriv 2 (fun y : ℝ => ψ y * (y : ℂ) ^ (s - 1)) x) := by
  rw [(integral_primitive_cutoff_cpow hψ hF hB hs).2]
  have he : (∫ x : ℝ in Ioi 0, iteratedDeriv 1 ψ x * (x : ℂ) ^ s) =
      mellin (iteratedDeriv 1 ψ) (s + 1) := by
    simp only [mellin, add_sub_cancel_right, smul_eq_mul, mul_comm]
  rw [he]
  unfold primitiveMellinTail
  ring

/-- The constant-term tail integral also converges for every complex parameter. -/
theorem integrable_cutoff_deriv_cpow {ψ : ℝ → ℂ} (hψ : IsMellinTailCutoff ψ) (s : ℂ) :
    IntegrableOn (fun x : ℝ => iteratedDeriv 1 ψ x * (x : ℂ) ^ s) (Ioi 0) := by
  have h := (hψ.mellin_mul_iteratedDeriv (F := fun _ => 1) continuous_const
    (by decide : 1 ≠ 0) (s + 1)).1
  simpa only [MellinConvergent, one_mul, add_sub_cancel_right, smul_eq_mul, mul_comm] using h

/-- Original-data capstone: an actual convergent smooth tail, holomorphic on the required half-plane. -/
theorem degreeTwoQuotient_primitiveMellinTail {g : ℕ → ℂ} {E : ℂ → ℂ}
    (hD : WeilZetaPower.ZetaPowerDatum 3 g E) (A : ℂ) {s : ℂ}
    (hs : s.re < 2) (hs0 : s ≠ 0) :
    AnalyticAt ℂ
      (primitiveMellinTail (fourierBoundaryPrimitive (degreeTwoQuotientCoeff g)) A mellinTailCutoff) s ∧
    IntegrableOn (fun x : ℝ => iteratedDeriv 1 mellinTailCutoff x * (x : ℂ) ^ s) (Ioi 0) ∧
    IntegrableOn (fun x : ℝ => fourierBoundaryPrimitive (degreeTwoQuotientCoeff g) x *
      iteratedDeriv 2 (fun y : ℝ => mellinTailCutoff y * (y : ℂ) ^ (s - 1)) x) (Ioi 0) ∧
    primitiveMellinTail (fourierBoundaryPrimitive (degreeTwoQuotientCoeff g)) A mellinTailCutoff s =
      -(A / s) * (∫ x : ℝ in Ioi 0, iteratedDeriv 1 mellinTailCutoff x * (x : ℂ) ^ s) +
      (∫ x : ℝ in Ioi 0, fourierBoundaryPrimitive (degreeTwoQuotientCoeff g) x *
        iteratedDeriv 2 (fun y : ℝ => mellinTailCutoff y * (y : ℂ) ^ (s - 1)) x) := by
  have hq := degreeTwoQuotientCoeff_summable_shift_square hD
  have hF := continuous_fourierBoundaryPrimitive hq
  have hB : ∃ C : ℝ, ∀ x, ‖fourierBoundaryPrimitive (degreeTwoQuotientCoeff g) x‖ ≤ C :=
    ⟨_, norm_fourierBoundaryPrimitive_le hq⟩
  have hψ := isMellinTailCutoff_mellinTailCutoff
  exact ⟨analyticAt_primitiveMellinTail hψ hF hB A hs hs0,
    integrable_cutoff_deriv_cpow hψ s,
    (integral_primitive_cutoff_cpow hψ hF hB hs).1,
    primitiveMellinTail_eq_integral hψ hF hB A hs⟩

end RHTower.WeilHigherDenominator
