import GaloisForLFunctions.HTGeometry.SymbolicRuellePollicott
import GaloisForLFunctions.RHTower.ZetaResidueFactorDerivative

/-!
# A Hölder realization of `ζ` is a zero-free strip

Let `φ ≥ r_min > 0` be a Hölder roof on a mixing subshift of finite type whose periodic-orbit sums
converge on `σ > 1`. The Ruelle–Pollicott continuation (`exists_holomorphic_reciprocal`) makes the
dynamical zeta function `exp Σ_n Z_n(s)/n` the reciprocal of a function `F` holomorphic on
`Re s > 1 − ε`.

**Theorem** (`riemannZeta_ne_zero_of_holderRealization`). If `ζ(s) = exp Σ_n Z_n(s)/n` on
`Re s > 1`, then `ζ` has no zero on `Re s > 1 − ε`. The residue factor `(s − 1)ζ(s)` and `F` are
holomorphic on the half-plane with product `s − 1` to the right of `1`, so by the identity theorem
everywhere on it.

So the strip comes from the continuation, not from oscillation: in a finite-type Hölder
realization the zeros of `ζ` are not resonances of the transfer operator at all. The whole
difficulty is the realization, which the conformal threshold restricts
(`one_le_mul_pow_of_cycleFamily`, `one_le_exp_mul_of_isPrimeLength`).
-/

open Filter Topology Complex
open GaloisForLFunctions.HTGeometry.Symbolic

namespace GaloisForLFunctions.ArithmeticResonanceTheory

/-- **Realization ⇒ strip.** A realization of `ζ` by a Hölder suspension of a mixing subshift of
finite type gives `ζ(s) ≠ 0` on a half-plane `Re s > 1 − ε`. -/
theorem riemannZeta_ne_zero_of_holderRealization {k : ℕ} {A : Fin k → Fin k → Prop} {M : ℕ}
    (hmix : IsMixing A M) (hM : 1 ≤ M) {φ : (ℕ → Fin k) → ℝ} {R₀ C θ : ℝ}
    (hφ : IsHolderPotential A φ R₀ C θ) (hR₀ : 0 ≤ R₀) (hC : 0 ≤ C) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    {rmin : ℝ} (hrmin : 0 < rmin) (hmin : ∀ y, IsAdmissible A y → rmin ≤ φ y)
    (hsum : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => periodicSumR A φ (n + 1) σ / ((n : ℝ) + 1))
    (hreal : ∀ s : ℂ, 1 < s.re →
      riemannZeta s = Complex.exp (∑' n : ℕ, periodicZ A φ (n + 1) s / ((n : ℂ) + 1))) :
    ∃ ε > 0, ∀ s : ℂ, 1 - ε < s.re → s ≠ 1 → riemannZeta s ≠ 0 := by
  obtain ⟨ε, hε, F, hF, hFeq⟩ :=
    exists_holomorphic_reciprocal hmix hM hφ hR₀ hC hθ0 hθ1 hrmin hmin hsum
  refine ⟨ε, hε, fun s hs hs1 hz => ?_⟩
  set U : Set ℂ := {s | 1 - ε < s.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  -- `(s − 1) ζ(s) F(s) = s − 1` to the right of `1`
  have hright : ∀ w : ℂ, 1 < w.re → RHTower.zetaResidueFactor w * F w = w - 1 := by
    intro w hw
    have hw1 : w ≠ 1 := fun h => by rw [h, Complex.one_re] at hw; exact lt_irrefl _ hw
    rw [RHTower.zetaResidueFactor_of_ne hw1, mul_assoc, hreal w hw, hFeq w hw, ← Complex.exp_add,
      add_neg_cancel, Complex.exp_zero, mul_one]
  have hf : AnalyticOnNhd ℂ (fun w => RHTower.zetaResidueFactor w * F w) U :=
    ((RHTower.differentiable_zetaResidueFactor.differentiableOn).mul hF).analyticOnNhd hUo
  have hg : AnalyticOnNhd ℂ (fun w : ℂ => w - 1) U :=
    (show Differentiable ℂ fun w : ℂ => w - 1 by fun_prop).differentiableOn.analyticOnNhd hUo
  set z₀ : ℂ := 2 with hz₀
  have hz₀U : z₀ ∈ U := by simp only [hU, Set.mem_setOf_eq, hz₀]; norm_num; linarith
  have hev : (fun w => RHTower.zetaResidueFactor w * F w) =ᶠ[𝓝 z₀] fun w => w - 1 := by
    have hopen : IsOpen {w : ℂ | 1 < w.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (show 1 < z₀.re by simp [hz₀])] with w hw
    exact hright w hw
  have heq := hf.eqOn_of_preconnected_of_eventuallyEq hg
    ((convex_halfSpace_re_gt (r := 1 - ε)).isPreconnected) hz₀U hev (show s ∈ U from hs)
  simp only [RHTower.zetaResidueFactor_of_ne hs1, hz, mul_zero, zero_mul] at heq
  exact hs1 (sub_eq_zero.mp heq.symm)

end GaloisForLFunctions.ArithmeticResonanceTheory
