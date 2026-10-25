import GaloisForLFunctions.RHTower.TheDampedMoebiusMellinQuotientIsHardyRightOfTheZeroAbscissa
import GaloisForLFunctions.RHTower.FermiNymanBeurlingHaarTarget
import GaloisForLFunctions.HTGeometry.MeromorphicLaurentTranslation

/-!
# The Fermi Mellin divisor subtracts shifted zeta orders

Below real part one, the dyadic eta factor is nonzero. Away from the
explicit scalar poles, the Fermi Mellin quotient therefore has exactly
the numerator zeta order minus the shifted denominator zeta order.
-/

noncomputable section
set_option autoImplicit false
open Complex Filter Topology

namespace RHTower

/-- Below real part one and away from the scalar poles, only the two zeta factors contribute to the divisor. -/
theorem meromorphicOrderAt_etaZetaQuotient {ε : ℝ} {s : ℂ}
    (hs0 : s ≠ 0) (hs : s.re < 1) (hsε : s + (ε : ℂ) ≠ 1) :
    meromorphicOrderAt (etaZetaQuotient ε) s =
      meromorphicOrderAt riemannZeta s - meromorphicOrderAt riemannZeta (s + ε) := by
  have hs1 : s ≠ 1 := by
    intro h
    rw [h, one_re] at hs
    exact (lt_irrefl 1) hs
  have hζ : AnalyticAt ℂ riemannZeta s := analyticOn_riemannZeta s hs1
  have hζε : AnalyticAt ℂ (fun z : ℂ => riemannZeta (z + ε)) s :=
    (analyticOn_riemannZeta (s + ε) hsε).comp
      (f := fun z : ℂ => z + ε) (analyticAt_id.add analyticAt_const)
  have hη : AnalyticAt ℂ (fun z : ℂ => 1 - (2 : ℂ) ^ (1 - z)) s :=
    differentiable_etaBase.analyticAt s
  -- The cleared and literal quotients agree near the selected point.
  have heq : etaZetaQuotient ε =ᶠ[𝓝 s]
      ((fun z : ℂ => 1 - (2 : ℂ) ^ (1 - z)) * riemannZeta /
        ((id : ℂ → ℂ) * (fun z : ℂ => riemannZeta (z + ε)))) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hs1,
      (isOpen_compl_singleton.preimage (continuous_id.add continuous_const)).mem_nhds hsε]
      with z hz1 hzε
    exact etaZetaQuotient_eq hz1 hzε
  rw [meromorphicOrderAt_congr (heq.filter_mono nhdsWithin_le_nhds),
    meromorphicOrderAt_div (hη.mul hζ).meromorphicAt (analyticAt_id.mul hζε).meromorphicAt,
    meromorphicOrderAt_mul_of_ne_zero hη (one_sub_two_cpow_ne_zero hs),
    meromorphicOrderAt_mul_of_ne_zero analyticAt_id hs0,
    GaloisForLFunctions.HTGeometry.meromorphicOrderAt_comp_add]

end RHTower

#print axioms RHTower.one_sub_two_cpow_ne_zero
#print axioms RHTower.meromorphicOrderAt_etaZetaQuotient
end
