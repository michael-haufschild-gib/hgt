import GaloisForLFunctions.RHTower.MobiusCausalSourceLimit

/-!
# Paper certificates: the centered-boundary and causal-graph limit laws

Formal certificates for
`docs/drafts/pipeline/2-fully-proven/not_new_scientific_knowledge/mobius/`
`mobius-schur-centered-boundary-limit-law.md` and
`mobius-schur-causal-critical-graph-limit-law.md`.

```text
centered-boundary law
  (3)  G_omega(z) = c_omega (1/zeta(1+2omega+z) - 1/zeta(1+2omega))/z ,
  (4)  G_0(z)     = 1/(z zeta(1+z)) ,
  (5)  G_omega -> G_0 in the boundary L^2 (Hardy) norm ,
  (11) G_0(z)     = (1/z) sum_n mu(n) n^{-1-z} ,
  (13) m_0(t)     = sum_{n <= e^t} mu(n)/n ,
  (14) m_0 in L^2(0,infinity)   [unconditional] ,
  (15) int |G_0(i tau)|^2 dtau = 2 pi int |m_0|^2 ,
  (16) L m_omega = G_omega on the imaginary axis ,
  (17) m_omega -> m_0 in L^2 .

causal-graph law
  (2)/(3) H_omega(z) = [zeta(1+z)/(1+omega+z) - c_omega/z]/zeta(1+2omega+z) ,
  (5)  M_omega = H_omega + G_omega ,
  (6)  H_0 = 1/(1+z) - G_0 ,
  (7)  H_omega -> H_0 in the boundary L^2 norm ,
  (13) G_omega -> G_0 ,
  (14) H_0 + G_0 = 1/(1+z) ,
  (15) L F_omega -> 1/(1+z) in the boundary L^2 norm ,
  (16) F_omega -> e^{-t} in L^2(0,infinity) for every causal realization.
```

Every statement is unconditional.  The RH-bearing gates of both cards (the pointed residue
extension of the continuation square, the nonexpansive pole-to-divisor covariance, the four-unit
boundary energy, RH) are untouched.
-/

open Complex MeasureTheory Set Filter ArithmeticFunction LSeries
open scoped BigOperators Topology LSeries.notation Moebius

noncomputable section
namespace RHTower

/-! ### The centered-boundary law -/

/-- **Card `(4)`.** -/
theorem centeredPaper_limit (z : ℂ) : centeredSchurLimit z = 1 / (z * riemannZeta (1 + z)) := rfl

/-- **Card `(5)`.** -/
theorem centeredPaper_hardy_limit :
    Tendsto (fun ω : ℝ => ∫ τ : ℝ, ‖centeredSchurQuotient ω ((τ : ℂ) * Complex.I) -
        centeredSchurLimit ((τ : ℂ) * Complex.I)‖ ^ 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
  tendsto_boundary_centeredSchur_energy

/-- **Card `(11)`.** -/
theorem centeredPaper_dirichlet {z : ℂ} (hz : 0 < z.re) (hz0 : z ≠ 0) :
    centeredSchurLimit z = (1 / z) * ∑' n : ℕ, LSeries.term (↗μ) (1 + z) n :=
  centeredSchurLimit_eq_lseries hz hz0

/-- **Card `(13)`.**  The critical inverse vector is the weighted Mertens function. -/
theorem centeredPaper_inverse_vector {t : ℝ} (ht : 0 < t) :
    criticalMertensVector t =
      ∑ n ∈ Finset.range (⌊Real.exp t⌋₊ + 1), mobiusRealWeight 1 n := by
  rw [criticalMertensVector, Set.indicator_of_mem (Set.mem_Ioi.mpr ht), mobiusWeightedPartial]

/-- **Card `(14)`.**  Unconditional `L²` membership of the critical boundary vector. -/
theorem centeredPaper_memLp : MemLp criticalMertensVector 2 volume :=
  memLp_criticalMertensVector

/-- **Card `(15)`.** -/
theorem centeredPaper_energy :
    (∫ τ : ℝ, ‖centeredSchurLimit ((τ : ℂ) * Complex.I)‖ ^ 2)
      = 2 * Real.pi * ∫ t : ℝ, ‖criticalMertensVector t‖ ^ 2 :=
  integral_norm_sq_criticalMertensVector

/-- **Card `(16)`.** -/
theorem centeredPaper_transfer {ω : ℝ} (hω : 0 < ω) {y : ℝ} (hy : y ≠ 0) :
    laplaceBoundary (centeredMertensVector ω) y
      = centeredSchurQuotient ω ((y : ℂ) * Complex.I) :=
  laplaceBoundary_centeredMertensVector hω hy

/-- **Card `(17)`.** -/
theorem centeredPaper_strong_limit :
    Tendsto (fun ν : ℝ => ∫ t : ℝ, ‖criticalMertensVector t - centeredMertensVector ν t‖ ^ 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
  tendsto_integral_norm_sq_criticalMertens_sub

/-! ### The causal-graph law -/

/-- **Card `(5)` of the causal-graph law.** -/
theorem causalPaper_split {ω : ℝ} (hω : 0 < ω) {z : ℂ} (hz : 0 ≤ z.re) (hz0 : z ≠ 0) :
    mobiusCausalMultiplier ω z = floorRemainderTransfer ω z + centeredSchurQuotient ω z :=
  mobiusCausalMultiplier_eq_add hω hz hz0

/-- **Card `(14)` of the causal-graph law.** -/
theorem causalPaper_cancellation (z : ℂ) :
    floorRemainderLimit z + centeredSchurLimit z = 1 / (1 + z) :=
  floorRemainderLimit_add_centeredSchurLimit z

/-- **Card `(7)` of the causal-graph law.** -/
theorem causalPaper_floorRemainder_limit :
    Tendsto (fun ω : ℝ => ∫ τ : ℝ, ‖floorRemainderTransfer ω ((τ : ℂ) * Complex.I) -
        floorRemainderLimit ((τ : ℂ) * Complex.I)‖ ^ 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
  tendsto_boundary_floorRemainder_energy

/-- **Card `(15)` of the causal-graph law.** -/
theorem causalPaper_multiplier_limit :
    Tendsto (fun ω : ℝ => ∫ τ : ℝ, ‖mobiusCausalMultiplier ω ((τ : ℂ) * Complex.I) -
        1 / (1 + (τ : ℂ) * Complex.I)‖ ^ 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
  tendsto_boundary_multiplier_energy

/-- **Card `(16)` of the causal-graph law.** -/
theorem causalPaper_time_domain_limit
    (F : ℝ → ℝ → ℂ)
    (hint : ∀ ω : ℝ, 0 < ω → Integrable (F ω))
    (hmem : ∀ ω : ℝ, 0 < ω → MemLp (F ω) 2 volume)
    (htrans : ∀ ω : ℝ, 0 < ω → ∀ y : ℝ, y ≠ 0 →
      laplaceBoundary (F ω) y = mobiusCausalMultiplier ω ((y : ℂ) * Complex.I)) :
    Tendsto (fun ω : ℝ => ∫ t : ℝ, ‖F ω t - causalPoleVector t‖ ^ 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
  tendsto_integral_norm_sq_causalSource_sub F hint hmem htrans

end RHTower
