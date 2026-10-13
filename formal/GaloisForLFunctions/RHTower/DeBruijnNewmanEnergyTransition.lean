import GaloisForLFunctions.RHTower.DeBruijnNonrealCountFinitenessTransition
import GaloisForLFunctions.HTGeometry.HeatFlowSquaredMajorization
import GaloisForLFunctions.HTGeometry.EntireZeroSumSemicontinuity

/-!
# Energy dissipation of the off-line zeros along the de Bruijn–Newman flow

For the de Bruijn–Newman flow `H_t` (`riemannHeat t`, `H_0 = Ξ`) and every threshold `c ≥ 0`,
the zeros `w` of `H_t` in the upper half-plane satisfy

`Σ_w mult(w) ((Im w)² − c)_+ ≤ Σ_{zeros ρ of Ξ, Im ρ > 0} ((Im ρ)² − 2t − c)_+`

(`riemannHeat_upper_energy_le`), for `0 < t` below the Gaussian-growth horizon
`8 S t < 1`, `S = 2 Σ_ρ |ρ|⁻²` (`xiApproxGrowth`).  The right side is a sum over the zero copies
of `Ξ` in the spectral coordinate, read as the supremum of its finite partial sums: the theorem
holds for every `K` bounding all finite partial sums, so it is unconditional.  With `c = 0` it
says that the squared heights of the upper zeros of `H_t` are dominated by those of `Ξ` reduced by
`2t`; with every `c` it is weak majorization.  If `Ξ` has only finitely many nonreal zeros the
right side is a finite sum (`riemannHeat_upper_energy_le_of_finite`).

**Proof.**  The polynomials `R_n = Ξ(0) ∏ (1 − z/a)` over closed finite zero sets
(`xiRealApprox`) have their upper roots among the upper zeros of `Ξ`, and the polynomial heat law
`sum_roots_polyHeat_sq_sub_le` bounds the root energy of `e^{−tD²}R_n`.  These heat flows
converge to `H_t` locally uniformly below the horizon (Gaussian averages of Gaussian-bounded
functions), and weighted zero sums are lower semicontinuous
(`sum_zeroMult_mul_le_of_tendstoLocallyUniformly`).
-/

open Complex Filter Topology Set Polynomial
open GaloisForLFunctions.HTGeometry

namespace RHTower.DeBruijn

noncomputable section

/-- The Gaussian-growth constant `S = 2 Σ_ρ |ρ|⁻²` of the approximants. -/
def xiApproxGrowth : ℝ := 2 * ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2

theorem xiApproxGrowth_nonneg : 0 ≤ xiApproxGrowth :=
  mul_nonneg zero_le_two (tsum_nonneg fun _ => by positivity)

/-- **The heat flows of the approximants converge to `H_t`** below the growth horizon. -/
theorem tendstoLocallyUniformly_polyHeat_xiRealApprox {t : ℝ} (ht : 0 < t)
    (htS : 8 * xiApproxGrowth * t < 1) :
    TendstoLocallyUniformly
      (fun n z => ((polyHeat t (xiRealApprox n)).map Complex.ofRealHom).eval z)
      (riemannHeat t) atTop := by
  have hS := xiApproxGrowth_nonneg
  have hC : 0 ≤ ‖XiC 0‖ := norm_nonneg _
  have hdom := norm_eval_map_xiRealApprox_le
  have hconv := tendstoLocallyUniformly_xiRealApprox
  have hH0 : ∀ w, ‖riemannHeat 0 w‖ ≤ ‖XiC 0‖ * Real.exp (xiApproxGrowth * ‖w‖ ^ 2) := fun w =>
    le_of_tendsto' ((TendstoLocallyUniformly.tendstoLocallyUniformlyOn hconv
      (s := Set.univ)).tendsto_at (Set.mem_univ w)).norm (fun n => hdom n w)
  have h := tendstoLocallyUniformly_gaussian_average
    (F := fun n z => ((xiRealApprox n).map Complex.ofRealHom).eval z) (f := riemannHeat 0)
    (fun n => Polynomial.continuous _) (differentiable_riemannHeat le_rfl).continuous hconv
    hC hS ht htS hdom hH0
  have e1 : (fun n z => ((polyHeat t (xiRealApprox n)).map Complex.ofRealHom).eval z) =
      fun n z => ∫ u : ℝ, (gaussDensity t u : ℂ) *
        ((xiRealApprox n).map Complex.ofRealHom).eval (z - I * u) := by
    funext n z; exact polyHeat_map_eval_eq_integral ht _ z
  have e2 : riemannHeat t = fun z => ∫ u : ℝ, (gaussDensity t u : ℂ) *
      riemannHeat 0 (z - I * u) := by
    funext z; exact riemannHeat_eq_integral_gaussian_shift ht z
  rw [e1, e2]
  exact h

/-- The upper roots of an approximant are the upper zero copies of its closed zero set. -/
theorem sum_upperRoots_xiRealApprox (n : ℕ) (f : ℂ → ℝ) :
    ((upperRoots (xiRealApprox n)).map f).sum =
      ∑ q ∈ (xiPairedCopyFinset (xiConjClosedFinset n)).filter
        (fun q => 0 < (xiSpectralPoint q).im), f (xiSpectralPoint q) := by
  classical
  rw [upperRoots, RiemannGaussian.realPolynomialUpperRootMultiset, map_xiRealApprox,
    roots_C_mul _ XiC_zero_ne_zero, roots_xiZeroPoly, Multiset.filter_map, Multiset.map_map,
    Finset.sum_eq_multiset_sum, Finset.filter_val]
  rfl

/-- **Energy dissipation along the de Bruijn–Newman flow.** -/
theorem riemannHeat_upper_energy_le {t c K : ℝ} (ht : 0 < t)
    (htS : 8 * xiApproxGrowth * t < 1) (hc : 0 ≤ c)
    (hK : ∀ T : Finset XiZeroCopy,
      ∑ q ∈ T.filter (fun q => 0 < (xiSpectralPoint q).im),
        max ((xiSpectralPoint q).im ^ 2 - 2 * t - c) 0 ≤ K)
    (Z : Finset ℂ) :
    ∑ w ∈ Z, (zeroMult (riemannHeat t) w : ℝ) * max ((max w.im 0) ^ 2 - c) 0 ≤ K := by
  refine sum_zeroMult_mul_le_of_tendstoLocallyUniformly (differentiable_riemannHeat ht.le)
    ⟨0, riemannHeat_zero_ne ht.le⟩ Z (tendstoLocallyUniformly_polyHeat_xiRealApprox ht htS)
    (by fun_prop) (fun w => le_max_right _ _) (Eventually.of_forall fun n => ?_)
  have h := sum_roots_polyHeat_sq_sub_le (xiRealApprox_ne_zero n) ht.le hc
  rw [sum_upperRoots_xiRealApprox] at h
  exact h.trans (hK _)

/-- **The finite case.**  If `Ξ` has finitely many nonreal zero copies, the energy of the upper
zeros of `H_t` is bounded by the finite sum over the upper zeros of `Ξ`. -/
theorem riemannHeat_upper_energy_le_of_finite
    (hfin : {q : XiZeroCopy | (xiSpectralPoint q).im ≠ 0}.Finite) {t c : ℝ} (ht : 0 < t)
    (htS : 8 * xiApproxGrowth * t < 1) (hc : 0 ≤ c) (Z : Finset ℂ) :
    ∑ w ∈ Z, (zeroMult (riemannHeat t) w : ℝ) * max ((max w.im 0) ^ 2 - c) 0 ≤
      ∑ q ∈ hfin.toFinset.filter (fun q => 0 < (xiSpectralPoint q).im),
        max ((xiSpectralPoint q).im ^ 2 - 2 * t - c) 0 := by
  classical
  refine riemannHeat_upper_energy_le ht htS hc (fun T => ?_) Z
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun q hq => ?_) fun _ _ _ => le_max_right _ _
  rw [Finset.mem_filter] at hq ⊢
  refine ⟨?_, hq.2⟩
  rw [Set.Finite.mem_toFinset]
  exact hq.2.ne'

end

end RHTower.DeBruijn
