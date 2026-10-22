import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerGaussianGreenPrimitive
import GaloisForLFunctions.RHTower.CompletedFluxPrimeArchDecomposition

/-!
# Deninger--Meyer singular Poisson--Gaussian lift

The Gaussian Green primitive has spectral denominator

`D_{c,ρ}(s) = exp ((ρ-c)² / (4π)) - exp ((s-c)² / (4π))`.

For `ρ ≠ c`, this denominator has a simple zero at `ρ`.  In the critical strip, Meyer's
Poisson boundary contributes the multiplier `ζ(s)`.  Consequently the forced local singular
preimage of the Gaussian Green germ is

`F_{c,ρ}(s) = (ζ(s) D_{c,ρ}(s))⁻¹`.

If `ρ` is a zero of `ξ` of multiplicity `m`, then `ζ` has the same order there and `F_{c,ρ}`
has exact pole order `m + 1`.  On a punctured neighbourhood, its Poisson image is exactly
`D_{c,ρ}⁻¹`, and multiplying once more by the Green denominator gives one.  This identifies the
precise successor principal part that any global Meyer source admission theorem must assemble;
it does not assume RH or the existence of such a global assembly.
-/

open Complex Filter Topology Set Metric
open scoped Real

namespace RHTower
namespace DeningerMeyerGaussianGreen

noncomputable section

/-- Complexified Mellin character of the normalized Gaussian heat step. -/
def gaussianMellinCharacter (c s : ℂ) : ℂ :=
  Complex.exp ((s - c) ^ (2 : ℕ) / (4 * (Real.pi : ℂ)))

/-- Resolvent denominator based at the spectral point `ρ`. -/
def gaussianResolventDenominator (c rho s : ℂ) : ℂ :=
  gaussianMellinCharacter c rho - gaussianMellinCharacter c s

theorem hasDerivAt_gaussianMellinCharacter (c s : ℂ) :
    HasDerivAt (gaussianMellinCharacter c)
      (gaussianMellinCharacter c s *
        ((s - c) / (2 * (Real.pi : ℂ)))) s := by
  change HasDerivAt (fun z : ℂ =>
    Complex.exp ((z - c) ^ (2 : ℕ) / (4 * (Real.pi : ℂ)))) _ s
  have hinner : HasDerivAt (fun z : ℂ =>
      (z - c) ^ (2 : ℕ) / (4 * (Real.pi : ℂ)))
      ((s - c) / (2 * (Real.pi : ℂ))) s := by
    convert (((hasDerivAt_id s).sub_const c).pow 2).div_const
      (4 * (Real.pi : ℂ)) using 1 <;> try rfl
    field_simp [Real.pi_ne_zero]
    simp only [id_eq]
    ring
  exact (Complex.hasDerivAt_exp _).comp s hinner

theorem analyticAt_gaussianMellinCharacter (c s : ℂ) :
    AnalyticAt ℂ (gaussianMellinCharacter c) s := by
  unfold gaussianMellinCharacter
  fun_prop

theorem hasDerivAt_gaussianResolventDenominator (c rho : ℂ) :
    HasDerivAt (gaussianResolventDenominator c rho)
      (-(gaussianMellinCharacter c rho *
        ((rho - c) / (2 * (Real.pi : ℂ))))) rho := by
  change HasDerivAt
    ((fun _ : ℂ => gaussianMellinCharacter c rho) - gaussianMellinCharacter c) _ rho
  simpa only [zero_sub] using
    (hasDerivAt_const rho (gaussianMellinCharacter c rho)).sub
      (hasDerivAt_gaussianMellinCharacter c rho)

@[simp] theorem gaussianResolventDenominator_self (c rho : ℂ) :
    gaussianResolventDenominator c rho rho = 0 := by
  simp [gaussianResolventDenominator]

theorem deriv_gaussianResolventDenominator_ne_zero
    {c rho : ℂ} (hcr : rho ≠ c) :
    deriv (gaussianResolventDenominator c rho) rho ≠ 0 := by
  rw [(hasDerivAt_gaussianResolventDenominator c rho).deriv]
  exact neg_ne_zero.mpr (mul_ne_zero (Complex.exp_ne_zero _)
    (div_ne_zero (sub_ne_zero.mpr hcr)
      (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))))

/-- The Gaussian Green denominator contributes exactly one local zero. -/
theorem analyticOrderAt_gaussianResolventDenominator_eq_one
    {c rho : ℂ} (hcr : rho ≠ c) :
    analyticOrderAt (gaussianResolventDenominator c rho) rho = 1 := by
  have hdenan : AnalyticAt ℂ (gaussianResolventDenominator c rho) rho := by
    unfold gaussianResolventDenominator gaussianMellinCharacter
    fun_prop
  apply hdenan.analyticOrderAt_eq_one_of_zero_deriv_ne_zero
  · exact gaussianResolventDenominator_self c rho
  · exact deriv_gaussianResolventDenominator_ne_zero hcr

/-- Forced local singular preimage under the Meyer Poisson multiplier and Gaussian resolvent. -/
def poissonGaussianSingularLift (c rho s : ℂ) : ℂ :=
  (riemannZeta s * gaussianResolventDenominator c rho s)⁻¹

/-- Exact local order of the singular lift throughout the open critical strip. -/
theorem meromorphicOrderAt_poissonGaussianSingularLift
    {c rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1) (hcr : rho ≠ c) :
    meromorphicOrderAt (poissonGaussianSingularLift c rho) rho =
      ((-(((analyticOrderAt xi rho).toNat : ℕ) + 1 : ℕ) : ℤ) : WithTop ℤ) := by
  have hzeta : AnalyticAt ℂ riemannZeta rho :=
    analyticOn_riemannZeta rho (by
      intro h
      subst rho
      norm_num at hstrip)
  have hden : AnalyticAt ℂ (gaussianResolventDenominator c rho) rho := by
    unfold gaussianResolventDenominator gaussianMellinCharacter
    fun_prop
  have hzetaOrder : analyticOrderAt riemannZeta rho =
      ((analyticOrderAt xi rho).toNat : ℕ∞) := by
    rw [← RHTower.xi_analyticOrderAt_eq_riemannZeta_of_mem_strip hstrip]
    exact (ENat.coe_toNat (xi_order_ne_top rho)).symm
  change meromorphicOrderAt
      ((fun s : ℂ => riemannZeta s * gaussianResolventDenominator c rho s)⁻¹) rho = _
  rw [meromorphicOrderAt_inv]
  change -meromorphicOrderAt
      (riemannZeta * gaussianResolventDenominator c rho) rho = _
  rw [meromorphicOrderAt_mul hzeta.meromorphicAt hden.meromorphicAt,
    hzeta.meromorphicOrderAt_eq, hden.meromorphicOrderAt_eq,
    hzetaOrder, analyticOrderAt_gaussianResolventDenominator_eq_one hcr]
  norm_num

/-- At a Xi zero of multiplicity `m ≥ 1`, the forced lift has pole order exactly `m + 1`. -/
theorem poissonGaussianSingularLift_successor_pole_at_xi_zero
    {c rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1)
    (hzero : xi rho = 0) (hcr : rho ≠ c) :
    meromorphicOrderAt (poissonGaussianSingularLift c rho) rho =
        ((-(((analyticOrderAt xi rho).toNat : ℕ) + 1 : ℕ) : ℤ) : WithTop ℤ) ∧
      1 ≤ (analyticOrderAt xi rho).toNat := by
  refine ⟨meromorphicOrderAt_poissonGaussianSingularLift hstrip hcr, ?_⟩
  rw [Nat.one_le_iff_ne_zero]
  intro hnat
  have horderNe : analyticOrderAt xi rho ≠ 0 :=
    analyticOrderAt_ne_zero.mpr ⟨xi_analyticOnNhd_univ rho (Set.mem_univ rho), hzero⟩
  apply horderNe
  rw [← ENat.coe_toNat (xi_order_ne_top rho), hnat]
  rfl

private theorem eventually_riemannZeta_ne_zero_of_mem_strip
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1) :
    ∀ᶠ s in 𝓝[≠] rho, riemannZeta s ≠ 0 := by
  have hzeta : AnalyticAt ℂ riemannZeta rho :=
    analyticOn_riemannZeta rho (by
      intro h
      subst rho
      norm_num at hstrip)
  have hzetaNotIdenticallyZero : analyticOrderAt riemannZeta rho ≠ ⊤ := by
    rw [← RHTower.xi_analyticOrderAt_eq_riemannZeta_of_mem_strip hstrip]
    exact xi_order_ne_top rho
  rcases hzeta.eventually_eq_zero_or_eventually_ne_zero with hlocal | hne
  · exact False.elim (hzetaNotIdenticallyZero (analyticOrderAt_eq_top.mpr hlocal))
  · exact hne

theorem eventually_gaussianResolventDenominator_ne_zero
    {c rho : ℂ} (hcr : rho ≠ c) :
    ∀ᶠ s in 𝓝[≠] rho, gaussianResolventDenominator c rho s ≠ 0 := by
  have hcoef :
      -(gaussianMellinCharacter c rho *
        ((rho - c) / (2 * (Real.pi : ℂ)))) ≠ 0 := by
    exact neg_ne_zero.mpr (mul_ne_zero (Complex.exp_ne_zero _)
      (div_ne_zero (sub_ne_zero.mpr hcr)
        (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))))
  exact (hasDerivAt_gaussianResolventDenominator c rho).eventually_ne (c := 0) hcoef

/-- On the punctured germ, Poisson transport followed by the Green denominator is exactly one. -/
theorem eventually_poissonGaussianSingularLift_anomaly
    {c rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1) (hcr : rho ≠ c) :
    ∀ᶠ s in 𝓝[≠] rho,
      riemannZeta s * gaussianResolventDenominator c rho s *
        poissonGaussianSingularLift c rho s = 1 := by
  filter_upwards [eventually_riemannZeta_ne_zero_of_mem_strip hstrip,
      eventually_gaussianResolventDenominator_ne_zero hcr] with s hzs hds
  rw [poissonGaussianSingularLift]
  exact mul_inv_cancel₀ (mul_ne_zero hzs hds)

/-- The Meyer Poisson image of the singular lift is exactly the Gaussian Green germ. -/
theorem eventually_poissonGaussianSingularLift_poisson_image
    {c rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1) (hcr : rho ≠ c) :
    ∀ᶠ s in 𝓝[≠] rho,
      riemannZeta s * poissonGaussianSingularLift c rho s =
        (gaussianResolventDenominator c rho s)⁻¹ := by
  filter_upwards [eventually_riemannZeta_ne_zero_of_mem_strip hstrip,
      eventually_gaussianResolventDenominator_ne_zero hcr] with s hzs hds
  rw [poissonGaussianSingularLift]
  field_simp

/-!
## Comparison with the completed Gamma boundary

The preceding lift contains a pole of order `m + 1` at a Xi zero of multiplicity `m`.  The
completed Xi factor cancels precisely the arithmetic `m` levels, leaving one universal Gaussian
Green pole.  Thus the Gamma/co-Poisson boundary sees a simple residue independently of Xi
multiplicity; the extra depth remains on the Meyer source side.
-/

/-- Completed Xi transport of the singular lift is exactly the Gamma factor times the Green germ. -/
theorem eventually_xi_mul_poissonGaussianSingularLift_eq_archFactor_mul_green
    {c rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1) (hcr : rho ≠ c) :
    ∀ᶠ s in 𝓝[≠] rho,
      xi s * poissonGaussianSingularLift c rho s =
        archFactor s * (gaussianResolventDenominator c rho s)⁻¹ := by
  let U : Set ℂ := {s | 0 < s.re ∧ s.re < 1}
  have hUopen : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hrhoU : rho ∈ U := hstrip
  have hstripEventually : ∀ᶠ s in 𝓝[≠] rho, s ∈ U :=
    Filter.Eventually.filter_mono inf_le_left (hUopen.mem_nhds hrhoU)
  filter_upwards [hstripEventually,
      eventually_poissonGaussianSingularLift_poisson_image hstrip hcr] with s hs hpoisson
  rw [xi_eq_archFactor_mul_zeta
      (by intro h; subst s; dsimp [U] at hs; norm_num at hs)
      (by intro h; subst s; dsimp [U] at hs; norm_num at hs)
      (Gammaℝ_ne_zero_of_re_pos hs.1)]
  rw [mul_assoc, hpoisson]

/-- Completed singular transport has one universal simple Green residue at every strip base point. -/
theorem meromorphicOrderAt_xi_mul_poissonGaussianSingularLift_eq_neg_one
    {c rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1)
    (hcr : rho ≠ c) :
    meromorphicOrderAt (fun s => xi s * poissonGaussianSingularLift c rho s) rho = -1 := by
  have hxi : AnalyticAt ℂ xi rho := xi_analyticOnNhd_univ rho (Set.mem_univ rho)
  have hzeta : AnalyticAt ℂ riemannZeta rho :=
    analyticOn_riemannZeta rho (by
      intro h
      subst rho
      norm_num at hstrip)
  have hden : AnalyticAt ℂ (gaussianResolventDenominator c rho) rho := by
    unfold gaussianResolventDenominator gaussianMellinCharacter
    fun_prop
  have hlift : MeromorphicAt (poissonGaussianSingularLift c rho) rho := by
    change MeromorphicAt
      ((fun s : ℂ => riemannZeta s * gaussianResolventDenominator c rho s)⁻¹) rho
    exact (hzeta.mul hden).meromorphicAt.inv
  change meromorphicOrderAt (xi * poissonGaussianSingularLift c rho) rho = -1
  rw [meromorphicOrderAt_mul hxi.meromorphicAt hlift,
    hxi.meromorphicOrderAt_eq,
    meromorphicOrderAt_poissonGaussianSingularLift hstrip hcr]
  have hfinite := ENat.coe_toNat (xi_order_ne_top rho)
  rw [← hfinite]
  simp only [ENat.map_coe, ENat.toNat_coe]
  change (((analyticOrderAt xi rho).toNat : ℤ) : WithTop ℤ) +
      ((-(((analyticOrderAt xi rho).toNat : ℤ) + 1) : ℤ) : WithTop ℤ) = -1
  rw [Int.neg_add, WithTop.coe_add]
  norm_num

end
end DeningerMeyerGaussianGreen
end RHTower
