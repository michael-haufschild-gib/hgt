import GaloisForLFunctions.ArithmeticIndexDescent.TheOrderedWeilSourceIsACenteredChebyshevDefect
import GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity.ThePoleCouplesTheLevelsHyperbolically

/-!
# Separated levels couple through the Chebyshev error

Two levels of a multiresolution with a gap between their supports couple through Weil's pairing.
ArithmeticIndexDescent splits an ordered pairing (`f` left of a cut `b`, `g` right of it) exactly:
one pole product cancels against the first Gamma mode, and

`W(f, g) = A(f)B(g) − P(f, g) − T(f, g) = −∫_0^∞ (ψ_err(h) − c) q'(h) dh − T(f, g)`,

with `P` the prime comb, `ψ_err` the Chebyshev error and `T` the Gamma tail. Here the gap
enters quantitatively:

* **The Gamma coupling decays geometrically with the gap**
  (`abs_orderedGammaTail_le_of_separated`): if `f` vanishes beyond `b − δ` and `g` before `b + δ`,
  `|T(f, g)| ≤ π e^{−4δ}(‖f‖² + ‖g‖²)`.
* **Separated levels couple through the Chebyshev error** (`abs_weilPair_add_chebyshev_le`):
  `W(f, g)` is the centered Chebyshev integral up to `π e^{−4δ}(‖f‖² + ‖g‖²)`.
* **On the pole hyperplane only the prime comb is left** (`abs_weilPair_add_primePart_le`): if
  `A(f) = 0`, then `W(f, g) = −P(f, g)` up to the same Gamma error.
* **Dyadic levels** (`abs_weilPair_shift_add_chebyshev_le`): copies of tests supported in
  `[0, ℓ]` at shifts `s` and `t ≥ s + ℓ` couple through the Chebyshev error up to
  `π e^{−2(t − s − ℓ)}(‖φ‖² + ‖ψ‖²)`; at dyadic levels `j < k` with `ℓ = log 2` this is
  `π 4^{−(k − j − 1)}`, a summable cost.

So between separated levels the archimedean place pays a summable cost, the pole couples
hyperbolically (`ThePoleCouplesTheLevelsHyperbolically`) and vanishes on the hyperplane, and the
whole arithmetic content of the coupling is the Chebyshev error at the lags between the levels.
-/

noncomputable section

open MeasureTheory Set Finset
open RHTower RHTower.WeilSpectral Zeta23

namespace GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity

open ArithmeticCastelnuovoSeveri ArithmeticIndexDescent

/-- ArithmeticCastelnuovoSeveri's `poleB` is the left pole moment `A`. -/
theorem poleB_eq_poleMomentA (f : ℝ → ℝ) : poleB f = poleMomentA f := by
  unfold poleB poleMomentA
  simp_rw [neg_div]

/-- ArithmeticCastelnuovoSeveri's `poleA` is the right pole moment `B`. -/
theorem poleA_eq_poleMomentB (f : ℝ → ℝ) : poleA f = poleMomentB f := rfl

theorem hasCompactSupport_const_mul_sq {f : ℝ → ℝ} (hfc : HasCompactSupport f) (c : ℝ) :
    HasCompactSupport (fun u => c * f u ^ 2) :=
  hfc.comp_left (g := fun x : ℝ => c * x ^ 2) (by simp)

/-- Damping by `e^{2(u − b)}` costs `e^{−4δ}` on functions vanishing beyond `b − δ`. -/
theorem leftBoundaryMass_le {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    {b δ : ℝ} (hsupp : ∀ u, b - δ < u → f u = 0) :
    leftBoundaryMass b f ≤ Real.exp (-(4 * δ)) * sectionMass f := by
  unfold leftBoundaryMass sectionMass
  rw [← integral_const_mul]
  refine integral_mono_of_nonneg (ae_of_all _ fun u => sq_nonneg _)
    ((continuous_const.mul (hf.pow 2)).integrable_of_hasCompactSupport
      (hasCompactSupport_const_mul_sq hfc _)) (ae_of_all _ fun u => ?_)
  by_cases hu : b - δ < u
  · simp [hsupp u hu]
  · have he : Real.exp (2 * (u - b)) ^ 2 ≤ Real.exp (-(4 * δ)) := by
      rw [sq, ← Real.exp_add]
      exact Real.exp_le_exp.mpr (by linarith [not_lt.mp hu])
    show (Real.exp (2 * (u - b)) * f u) ^ 2 ≤ Real.exp (-(4 * δ)) * f u ^ 2
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right he (sq_nonneg _)

/-- Damping by `e^{−2(u − b)}` costs `e^{−4δ}` on functions vanishing before `b + δ`. -/
theorem rightBoundaryMass_le {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    {b δ : ℝ} (hsupp : ∀ u, u < b + δ → g u = 0) :
    rightBoundaryMass b g ≤ Real.exp (-(4 * δ)) * sectionMass g := by
  unfold rightBoundaryMass sectionMass
  rw [← integral_const_mul]
  refine integral_mono_of_nonneg (ae_of_all _ fun u => sq_nonneg _)
    ((continuous_const.mul (hg.pow 2)).integrable_of_hasCompactSupport
      (hasCompactSupport_const_mul_sq hgc _)) (ae_of_all _ fun u => ?_)
  by_cases hu : u < b + δ
  · simp [hsupp u hu]
  · have he : Real.exp (-2 * (u - b)) ^ 2 ≤ Real.exp (-(4 * δ)) := by
      rw [sq, ← Real.exp_add]
      exact Real.exp_le_exp.mpr (by linarith [not_lt.mp hu])
    show (Real.exp (-2 * (u - b)) * g u) ^ 2 ≤ Real.exp (-(4 * δ)) * g u ^ 2
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right he (sq_nonneg _)

theorem left_of_separated {f : ℝ → ℝ} {b δ : ℝ} (hδ : 0 < δ)
    (hsupp : ∀ u, b - δ < u → f u = 0) : ∀ u, b ≤ u → f u = 0 :=
  fun u hu => hsupp u (by linarith)

theorem right_of_separated {g : ℝ → ℝ} {b δ : ℝ} (hδ : 0 < δ)
    (hsupp : ∀ u, u < b + δ → g u = 0) : ∀ u, u ≤ b → g u = 0 :=
  fun u hu => hsupp u (by linarith)

/-- **The Gamma coupling decays geometrically with the gap**:
`|T(f, g)| ≤ π e^{−4δ}(‖f‖² + ‖g‖²)` when `f` vanishes beyond `b − δ` and `g` before `b + δ`. -/
theorem abs_orderedGammaTail_le_of_separated {f g : ℝ → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (hg : Continuous g) (hgc : HasCompactSupport g) {b δ : ℝ}
    (hδ : 0 < δ) (hleft : ∀ u, b - δ < u → f u = 0) (hright : ∀ u, u < b + δ → g u = 0) :
    |orderedGammaTail f g| ≤ Real.pi * Real.exp (-(4 * δ)) * (sectionMass f + sectionMass g) := by
  have h := abs_orderedGammaTail_le_boundaryMass hf hfc hg hgc (left_of_separated hδ hleft)
    (right_of_separated hδ hright)
  have hl := leftBoundaryMass_le hf hfc hleft
  have hr := rightBoundaryMass_le hg hgc hright
  calc |orderedGammaTail f g| ≤ Real.pi * (leftBoundaryMass b f + rightBoundaryMass b g) := h
    _ ≤ Real.pi * (Real.exp (-(4 * δ)) * sectionMass f + Real.exp (-(4 * δ)) * sectionMass g) :=
        mul_le_mul_of_nonneg_left (add_le_add hl hr) Real.pi_pos.le
    _ = _ := by ring

/-- **Separated levels couple through the Chebyshev error**: for every centering `c`,
`|W(f, g) + ∫_0^∞ (ψ_err(h) − c) q'(h) dh| ≤ π e^{−4δ}(‖f‖² + ‖g‖²)`. -/
theorem abs_weilPair_add_chebyshev_le (f g : realTests) {b δ : ℝ} (hδ : 0 < δ)
    (hleft : ∀ u, b - δ < u → f.1 u = 0) (hright : ∀ u, u < b + δ → g.1 u = 0) (c : ℝ) :
    |realWeilForm f g + ∫ h in Ioi (0 : ℝ), (ArithmeticIncidencePositivity.chebyshevError h - c) *
        deriv (orderedSourceLagWeight f.1 g.1) h| ≤
      Real.pi * Real.exp (-(4 * δ)) * (sectionMass f.1 + sectionMass g.1) := by
  rw [realWeilForm_ordered_eq_centered_chebyshev f g (left_of_separated hδ hleft)
    (right_of_separated hδ hright) c, show ∀ x y : ℝ, -x - y + x = -y by intros; ring, abs_neg]
  exact abs_orderedGammaTail_le_of_separated f.2.1.continuous f.2.2 g.2.1.continuous g.2.2 hδ
    hleft hright

/-- The separated coupling is the uncancelled pole product minus the prime comb, up to
`π e^{−4δ}(‖f‖² + ‖g‖²)`. -/
theorem abs_weilPair_sub_pole_add_primePart_le (f g : realTests) {b δ : ℝ} (hδ : 0 < δ)
    (hleft : ∀ u, b - δ < u → f.1 u = 0) (hright : ∀ u, u < b + δ → g.1 u = 0) :
    |realWeilForm f g - poleMomentA f.1 * poleMomentB g.1 +
        (primePart (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
          (EF.weilTest (cx f.1) (cx g.1))).re| ≤
      Real.pi * Real.exp (-(4 * δ)) * (sectionMass f.1 + sectionMass g.1) := by
  rw [realWeilForm_ordered_pole_cancellation f g (left_of_separated hδ hleft)
    (right_of_separated hδ hright), poleB_eq_poleMomentA, poleA_eq_poleMomentB]
  rw [show ∀ x y z : ℝ, x - y - z - x + y = -z by intros; ring, abs_neg]
  exact abs_orderedGammaTail_le_of_separated f.2.1.continuous f.2.2 g.2.1.continuous g.2.2 hδ
    hleft hright

/-- **On the pole hyperplane only the prime comb is left**: if the lower level has `A(f) = 0`,
then `|W(f, g) + P(f, g)| ≤ π e^{−4δ}(‖f‖² + ‖g‖²)`. -/
theorem abs_weilPair_add_primePart_le (f g : realTests) {b δ : ℝ} (hδ : 0 < δ)
    (hleft : ∀ u, b - δ < u → f.1 u = 0) (hright : ∀ u, u < b + δ → g.1 u = 0)
    (hA : poleMomentA f.1 = 0) :
    |realWeilForm f g + (primePart (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest (cx f.1) (cx g.1))).re| ≤
      Real.pi * Real.exp (-(4 * δ)) * (sectionMass f.1 + sectionMass g.1) := by
  have h := abs_weilPair_sub_pole_add_primePart_le f g hδ hleft hright
  rwa [hA, zero_mul, sub_zero] at h

/-- The copy `φ(· − t)` of a real test. -/
def shiftTest (t : ℝ) (φ : realTests) : realTests :=
  ⟨fun u => φ.1 (u - t), φ.2.1.comp (contDiff_id.sub contDiff_const),
    φ.2.2.comp_homeomorph (Homeomorph.subRight t)⟩

theorem sectionMass_shift (t : ℝ) (φ : ℝ → ℝ) :
    sectionMass (fun u => φ (u - t)) = sectionMass φ :=
  integral_sub_right_eq_self (fun u => φ u ^ 2) t

/-- **Separated copies couple through the Chebyshev error.** If `φ, ψ` vanish outside `[0, ℓ]`
and `s + ℓ < t`, the copies at `s` and `t` satisfy
`|W + ∫_0^∞ (ψ_err − c) q'| ≤ π e^{−2(t − s − ℓ)}(‖φ‖² + ‖ψ‖²)`. At dyadic levels `j < k`,
`ℓ = log 2`, the factor is `4^{−(k − j − 1)}`. -/
theorem abs_weilPair_shift_add_chebyshev_le (φ ψ : realTests) {ℓ s t : ℝ}
    (hφ : ∀ u, u ∉ Icc 0 ℓ → φ.1 u = 0) (hψ : ∀ u, u ∉ Icc 0 ℓ → ψ.1 u = 0) (hst : s + ℓ < t)
    (c : ℝ) :
    |realWeilForm (shiftTest s φ) (shiftTest t ψ) +
        ∫ h in Ioi (0 : ℝ), (ArithmeticIncidencePositivity.chebyshevError h - c) *
          deriv (orderedSourceLagWeight (shiftTest s φ).1 (shiftTest t ψ).1) h| ≤
      Real.pi * Real.exp (-(2 * (t - s - ℓ))) * (sectionMass φ.1 + sectionMass ψ.1) := by
  have hδ : 0 < (t - s - ℓ) / 2 := by linarith
  have h := abs_weilPair_add_chebyshev_le (shiftTest s φ) (shiftTest t ψ)
    (b := (s + ℓ + t) / 2) hδ
    (fun u hu => hφ (u - s) fun hm => by linarith [(mem_Icc.mp hm).2])
    (fun u hu => hψ (u - t) fun hm => by linarith [(mem_Icc.mp hm).1]) c
  rwa [show 4 * ((t - s - ℓ) / 2) = 2 * (t - s - ℓ) by ring, shiftTest, shiftTest,
    sectionMass_shift, sectionMass_shift] at h

/-- The dyadic Gamma factor: `e^{−2(k − j − 1) log 2} = 4^{−(k − j − 1)}`. -/
theorem exp_neg_two_mul_dyadic_gap (d : ℕ) :
    Real.exp (-(2 * (d * Real.log 2))) = (1 / 4) ^ d := by
  have h4 : Real.log (1 / 4) = -(2 * Real.log 2) := by
    rw [one_div, Real.log_inv, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  rw [show -(2 * (d * Real.log 2)) = d * Real.log (1 / 4) by rw [h4]; ring, Real.exp_nat_mul,
    Real.exp_log (by norm_num)]

end GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity
