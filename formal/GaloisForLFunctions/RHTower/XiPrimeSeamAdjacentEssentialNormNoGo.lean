import GaloisForLFunctions.RHTower.XiPrimeSeamSparseEdgeCalkin
import GaloisForLFunctions.RHTower.SoninEulerEssentialNorm

/-!
# Adjacent-prime asymptotic Calkin smallness is automatic

Exact compactness of an adjacent seam coboundary forces equality of its two seam values.
In contrast, its *essential norm* is the seam jump divided by the positive Euler scale.
Both seam values tend to zero along the prime ray at every strip point, including a
hypothetical off-critical zero. Thus asymptotic adjacent Calkin smallness, even after
removing the Euler attenuation, cannot replace exact compactness in the SEC route.
-/

open Filter Topology

namespace RHTower

/-- Sharp Calkin norm of a single adjacent or nonadjacent seam edge. -/
theorem essentialNorm_primeSeamCoboundary_exact
    {a : ℝ} (ha : 0 < a) (rho : ℂ) (p q : Nat.Primes) :
    essentialNorm (primeSeamCoboundary a rho p q) =
      ‖orbitwiseNatPrimeSeamCharge (p : ℕ) rho -
        orbitwiseNatPrimeSeamCharge (q : ℕ) rho‖ /
        (Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ)) := by
  unfold primeSeamCoboundary xiSeamCoboundaryCorner
  rw [essentialNorm_smul,
    essentialNorm_evenCentralPositiveEulerQuadraticCorner a (p : ℝ) (q : ℝ)
      ha (one_lt_natPrime_cast p) (one_lt_natPrime_cast q)]
  ring

/-- Every strip point has asymptotically Calkin-small adjacent prime edges. This
does not distinguish critical from off-critical points. -/
theorem tendsto_primeRay_adjacent_essentialNorm_zero
    {a : ℝ} (ha : 0 < a) (rho : ℂ)
    (hstrip : 0 < rho.re ∧ rho.re < 1) :
    Tendsto (fun n : ℕ => essentialNorm
      (primeSeamCoboundary a rho (primeRayPoint n) (primeRayPoint (n + 1))))
      atTop (nhds 0) := by
  have hprime : Tendsto primeRay atTop atTop := primeRay_strictMono.tendsto_atTop
  have hleft : Tendsto (fun n : ℕ => orbitwiseNatPrimeSeamCharge (primeRay n) rho)
      atTop (nhds 0) := (tendsto_orbitwiseNatPrimeSeamCharge hstrip).comp hprime
  have hright : Tendsto (fun n : ℕ => orbitwiseNatPrimeSeamCharge (primeRay (n + 1)) rho)
      atTop (nhds 0) := by
    exact hleft.comp (tendsto_add_atTop_nat 1)
  have hdiff : Tendsto (fun n : ℕ =>
      ‖orbitwiseNatPrimeSeamCharge (primeRay n) rho -
        orbitwiseNatPrimeSeamCharge (primeRay (n + 1)) rho‖)
      atTop (nhds 0) := by
    convert (hleft.sub hright).norm using 1; simp
  apply squeeze_zero' (Filter.Eventually.of_forall fun n =>
    essentialNorm_nonneg _) (Filter.Eventually.of_forall fun n => ?_) hdiff
  rw [essentialNorm_primeSeamCoboundary_exact ha rho (primeRayPoint n)
    (primeRayPoint (n + 1))]
  simp only [primeRayPoint_coe]
  have hden : 1 ≤ Real.sqrt (primeRay n : ℝ) *
      Real.sqrt (primeRay (n + 1) : ℝ) := by
    have hp : (1 : ℝ) ≤ Real.sqrt (primeRay n : ℝ) := by
      apply Real.one_le_sqrt.mpr
      exact_mod_cast (primeRay_prime n).one_lt.le
    have hq : (1 : ℝ) ≤ Real.sqrt (primeRay (n + 1) : ℝ) := by
      apply Real.one_le_sqrt.mpr
      exact_mod_cast (primeRay_prime (n + 1)).one_lt.le
    nlinarith
  exact div_le_self (norm_nonneg _) hden

/-- Even multiplying by the full positive-Euler scale does not make adjacent
asymptotic Calkin smallness selective: the normalized essential norm is
exactly the difference of two seam charges, both of which vanish cofinally. -/
theorem tendsto_primeRay_adjacent_scaledEssentialNorm_zero
    {a : ℝ} (ha : 0 < a) (rho : ℂ)
    (hstrip : 0 < rho.re ∧ rho.re < 1) :
    Tendsto (fun n : ℕ =>
      (Real.sqrt (primeRay n : ℝ) * Real.sqrt (primeRay (n + 1) : ℝ)) *
        essentialNorm
          (primeSeamCoboundary a rho (primeRayPoint n) (primeRayPoint (n + 1))))
      atTop (nhds 0) := by
  have hprime : Tendsto primeRay atTop atTop := primeRay_strictMono.tendsto_atTop
  have hleft : Tendsto (fun n : ℕ => orbitwiseNatPrimeSeamCharge (primeRay n) rho)
      atTop (nhds 0) := (tendsto_orbitwiseNatPrimeSeamCharge hstrip).comp hprime
  have hright : Tendsto (fun n : ℕ => orbitwiseNatPrimeSeamCharge (primeRay (n + 1)) rho)
      atTop (nhds 0) := hleft.comp (tendsto_add_atTop_nat 1)
  convert (hleft.sub hright).norm using 1
  · ext n
    rw [essentialNorm_primeSeamCoboundary_exact ha rho (primeRayPoint n)
      (primeRayPoint (n + 1))]
    simp only [primeRayPoint_coe]
    have hp : 0 < Real.sqrt (primeRay n : ℝ) :=
      Real.sqrt_pos.mpr (by exact_mod_cast (primeRay_prime n).pos)
    have hq : 0 < Real.sqrt (primeRay (n + 1) : ℝ) :=
      Real.sqrt_pos.mpr (by exact_mod_cast (primeRay_prime (n + 1)).pos)
    field_simp
  · simp

end RHTower
