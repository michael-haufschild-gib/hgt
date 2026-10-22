import GaloisForLFunctions.RHTower.L2FourierEndpointOrthogonality
import GaloisForLFunctions.RHTower.Suzuki.SuzukiHlogEndpointSupport
import GaloisForLFunctions.RHTower.XiShiftedHardEdgeOddFirstFailurePrimePowerJump

/-!
# Route U: endpoint invisibility of the entering prime-wall atom

At the hard-edge wall σ = log(n)/2, the newly entering source atom has physical frequency
log(n) = 2σ. An admitted odd state x ↦ x H(x²) of Paley--Wiener type σ has mathlib Fourier
support in [-σ/(2π), σ/(2π)]. The square of that state has no Fourier mass at the extreme
difference frequency 2σ: the two support intervals meet only at one Lebesgue-null endpoint.

Consequently the exact n-th prime-jump response vanishes, not merely has a controlled sign.
The literal odd quadratic form is unchanged across the n-th wall for every such admitted state.
This closes the source-orientation obstruction at each individual prime-power wall; any remaining
Route-U gap must lie in admission/form-domain passage to the wall, not in the finite-prime jump.
-/

noncomputable section

open MeasureTheory Set FourierTransform
open GaloisForLFunctions.HTGeometry

namespace RHTower

/-- The prime atom entering a Route-U hard-edge wall is invisible to any admitted odd state whose
Fourier transform is supported in the wall's Paley--Wiener band. -/
theorem routeUHardEdgePrimeJumpOddResponse_eq_zero_of_bandSupport
    {n : ℕ} (hn : 2 ≤ n) {H : ℝ → ℝ}
    (hg : MemLp (fun x : ℝ => x * H (x ^ (2 : ℕ))) 2 volume)
    (hband : ∀ᵐ ξ : ℝ, Real.log n / (4 * Real.pi) < |ξ| →
      (𝓕 (ofRealLp (hg.toLp (fun x : ℝ => x * H (x ^ (2 : ℕ))))) :
        Lp ℂ 2 (volume : Measure ℝ)) ξ = 0) :
    routeUHardEdgePrimeJumpOddResponse n H H = 0 := by
  have hnreal : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos hnreal
  have hb : 0 ≤ Real.log (n : ℝ) / (4 * Real.pi) := by positivity
  have hendpoint := MellinL2.integral_sq_mul_cos_four_pi_eq_zero_of_bandSupport
    hb hg hband
  have hscale : 4 * Real.pi * (Real.log (n : ℝ) / (4 * Real.pi)) =
      Real.log (n : ℝ) := by
    field_simp [Real.pi_ne_zero]
  have hendpoint' :
      (∫ x : ℝ, (x * H (x ^ (2 : ℕ))) ^ (2 : ℕ) * Real.cos (Real.log n * x)) = 0 := by
    simpa only [hscale] using hendpoint
  have hcos :
      (∫ x : ℝ, (x * H (x ^ (2 : ℕ))) ^ (2 : ℕ) * Real.cos (x * Real.log n)) = 0 := by
    rw [show (fun x : ℝ => (x * H (x ^ (2 : ℕ))) ^ (2 : ℕ) * Real.cos (x * Real.log n)) =
        fun x : ℝ => (x * H (x ^ (2 : ℕ))) ^ (2 : ℕ) * Real.cos (Real.log n * x) by
      funext x
      rw [mul_comm x (Real.log n)]]
    exact hendpoint'
  unfold routeUHardEdgePrimeJumpOddResponse
  have hsub := integral_comp_sq_eq_integral_Ioi
    (fun u : ℝ => u * (H u * H u) * routeUHardEdgePrimeJumpDensity n (Real.sqrt u))
  rw [← hsub]
  calc
    (∫ x : ℝ, x ^ (2 : ℕ) * (H (x ^ (2 : ℕ)) * H (x ^ (2 : ℕ))) *
        routeUHardEdgePrimeJumpDensity n (Real.sqrt (x ^ (2 : ℕ)))) =
      ∫ x : ℝ, ((ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n) *
        ((x * H (x ^ (2 : ℕ))) ^ (2 : ℕ) * Real.cos (x * Real.log n)) := by
          apply integral_congr_ae
          filter_upwards with x
          rw [routeUHardEdgePrimeJumpDensity, Real.sqrt_sq_eq_abs]
          have hcosabs : Real.cos (|x| * Real.log n) =
              Real.cos (x * Real.log n) := by
            rcases abs_choice x with h | h
            · rw [h]
            · rw [h, neg_mul, Real.cos_neg]
          rw [hcosabs]
          ring
    _ = ((ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n) *
        ∫ x : ℝ, (x * H (x ^ (2 : ℕ))) ^ (2 : ℕ) * Real.cos (x * Real.log n) := by
          rw [integral_const_mul]
    _ = 0 := by rw [hcos, mul_zero]

/-- Source-domain form of endpoint invisibility. Once the odd descendant is genuinely admitted
to Suzuki's logarithmic form domain at the prime-wall aperture, its prime-jump response vanishes;
no separate support premise remains. -/
theorem routeUHardEdgePrimeJumpOddResponse_eq_zero_of_suzukiHlogAdmission
    {n : ℕ} (hn : 2 ≤ n) {H : ℝ → ℝ}
    (hg : MemLp (fun x : ℝ => x * H (x ^ (2 : ℕ))) 2 volume)
    (a : SuzukiPositiveAperture)
    (ha : a.1 = Real.log n / (4 * Real.pi))
    (q : SuzukiHlogFormDomain a)
    (hq : suzukiHlogWeightedToL2 q.1 =
      ofRealLp (hg.toLp (fun x : ℝ => x * H (x ^ (2 : ℕ))))) :
    routeUHardEdgePrimeJumpOddResponse n H H = 0 := by
  apply routeUHardEdgePrimeJumpOddResponse_eq_zero_of_bandSupport hn hg
  have hs := suzukiHlogFormDomain_fourier_bandSupport a q
  rw [hq] at hs
  simpa only [ha] using hs

/-- At a hard-edge wall, the exact entering prime atom does not change the odd quadratic form of
an admitted endpoint-bandlimited state. -/
theorem routeUHardEdgeOddForm_log_nat_half_eq_incoming_of_bandSupport
    {n : ℕ} (hn : 2 ≤ n) {H : ℝ → ℝ}
    (hbase : IntegrableOn (fun u : ℝ =>
      u * (H u * H u) *
        routeUHardEdgeDensity (routeUHardEdgeIncomingAperture n) (Real.sqrt u) /
          Real.sqrt u) (Ioi 0))
    (hjump : IntegrableOn (fun u : ℝ =>
      u * (H u * H u) * routeUHardEdgePrimeJumpDensity n (Real.sqrt u) /
        Real.sqrt u) (Ioi 0))
    (hg : MemLp (fun x : ℝ => x * H (x ^ (2 : ℕ))) 2 volume)
    (hband : ∀ᵐ ξ : ℝ, Real.log n / (4 * Real.pi) < |ξ| →
      (𝓕 (ofRealLp (hg.toLp (fun x : ℝ => x * H (x ^ (2 : ℕ))))) :
        Lp ℂ 2 (volume : Measure ℝ)) ξ = 0) :
    routeUHardEdgeOddForm (Real.log n / 2) H H =
      routeUHardEdgeOddForm (routeUHardEdgeIncomingAperture n) H H := by
  rw [routeUHardEdgeOddForm_log_nat_half_eq_incoming_sub_primeJumpResponse
    hn H H hbase hjump,
    routeUHardEdgePrimeJumpOddResponse_eq_zero_of_bandSupport hn hg hband,
    sub_zero]

/-- Endpoint Paley--Wiener support rules out a negative odd-form jump at every literal Route-U
prime wall. -/
theorem routeUHardEdgeOddForm_log_nat_half_nonneg_of_incoming_and_bandSupport
    {n : ℕ} (hn : 2 ≤ n) {H : ℝ → ℝ}
    (hbase : IntegrableOn (fun u : ℝ =>
      u * (H u * H u) *
        routeUHardEdgeDensity (routeUHardEdgeIncomingAperture n) (Real.sqrt u) /
          Real.sqrt u) (Ioi 0))
    (hjump : IntegrableOn (fun u : ℝ =>
      u * (H u * H u) * routeUHardEdgePrimeJumpDensity n (Real.sqrt u) /
        Real.sqrt u) (Ioi 0))
    (hg : MemLp (fun x : ℝ => x * H (x ^ (2 : ℕ))) 2 volume)
    (hband : ∀ᵐ ξ : ℝ, Real.log n / (4 * Real.pi) < |ξ| →
      (𝓕 (ofRealLp (hg.toLp (fun x : ℝ => x * H (x ^ (2 : ℕ))))) :
        Lp ℂ 2 (volume : Measure ℝ)) ξ = 0)
    (hincoming : 0 ≤ routeUHardEdgeOddForm (routeUHardEdgeIncomingAperture n) H H) :
    0 ≤ routeUHardEdgeOddForm (Real.log n / 2) H H := by
  rw [routeUHardEdgeOddForm_log_nat_half_eq_incoming_of_bandSupport
    hn hbase hjump hg hband]
  exact hincoming

/-- The prime atom entering a Route-U wall has zero mixed response between any two states sharing
the endpoint Paley--Wiener band. -/
theorem routeUHardEdgePrimeJumpOddResponse_eq_zero_of_two_bandSupports
    {n : ℕ} (hn : 2 ≤ n) {H K : ℝ → ℝ}
    (hg : MemLp (fun x : ℝ => x * H (x ^ (2 : ℕ))) 2 volume)
    (hk : MemLp (fun x : ℝ => x * K (x ^ (2 : ℕ))) 2 volume)
    (hbandg : ∀ᵐ ξ : ℝ, Real.log n / (4 * Real.pi) < |ξ| →
      (𝓕 (ofRealLp (hg.toLp (fun x : ℝ => x * H (x ^ (2 : ℕ))))) :
        Lp ℂ 2 (volume : Measure ℝ)) ξ = 0)
    (hbandk : ∀ᵐ ξ : ℝ, Real.log n / (4 * Real.pi) < |ξ| →
      (𝓕 (ofRealLp (hk.toLp (fun x : ℝ => x * K (x ^ (2 : ℕ))))) :
        Lp ℂ 2 (volume : Measure ℝ)) ξ = 0) :
    routeUHardEdgePrimeJumpOddResponse n H K = 0 := by
  have hnreal : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos hnreal
  have hb : 0 ≤ Real.log (n : ℝ) / (4 * Real.pi) := by positivity
  have hendpoint :=
    MellinL2.integral_mul_mul_cos_four_pi_eq_zero_of_two_bandSupports
      hb hg hk hbandg hbandk
  have hscale : 4 * Real.pi * (Real.log (n : ℝ) / (4 * Real.pi)) =
      Real.log (n : ℝ) := by
    field_simp [Real.pi_ne_zero]
  have hendpoint' :
      (∫ x : ℝ, ((x * H (x ^ (2 : ℕ))) * (x * K (x ^ (2 : ℕ)))) *
        Real.cos (Real.log n * x)) = 0 := by
    simpa only [hscale] using hendpoint
  have hcos :
      (∫ x : ℝ, ((x * H (x ^ (2 : ℕ))) * (x * K (x ^ (2 : ℕ)))) *
        Real.cos (x * Real.log n)) = 0 := by
    rw [show (fun x : ℝ => ((x * H (x ^ (2 : ℕ))) * (x * K (x ^ (2 : ℕ)))) *
          Real.cos (x * Real.log n)) =
        fun x : ℝ => ((x * H (x ^ (2 : ℕ))) * (x * K (x ^ (2 : ℕ)))) *
          Real.cos (Real.log n * x) by
      funext x
      rw [mul_comm x (Real.log n)]]
    exact hendpoint'
  unfold routeUHardEdgePrimeJumpOddResponse
  have hsub := integral_comp_sq_eq_integral_Ioi
    (fun u : ℝ => u * (H u * K u) * routeUHardEdgePrimeJumpDensity n (Real.sqrt u))
  rw [← hsub]
  calc
    (∫ x : ℝ, x ^ (2 : ℕ) * (H (x ^ (2 : ℕ)) * K (x ^ (2 : ℕ))) *
        routeUHardEdgePrimeJumpDensity n (Real.sqrt (x ^ (2 : ℕ)))) =
      ∫ x : ℝ, ((ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n) *
        (((x * H (x ^ (2 : ℕ))) * (x * K (x ^ (2 : ℕ)))) *
          Real.cos (x * Real.log n)) := by
          apply integral_congr_ae
          filter_upwards with x
          rw [routeUHardEdgePrimeJumpDensity, Real.sqrt_sq_eq_abs]
          have hcosabs : Real.cos (|x| * Real.log n) =
              Real.cos (x * Real.log n) := by
            rcases abs_choice x with h | h
            · rw [h]
            · rw [h, neg_mul, Real.cos_neg]
          rw [hcosabs]
          ring
    _ = ((ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n) *
        ∫ x : ℝ, ((x * H (x ^ (2 : ℕ))) * (x * K (x ^ (2 : ℕ)))) *
          Real.cos (x * Real.log n) := by
          rw [integral_const_mul]
    _ = 0 := by rw [hcos, mul_zero]

/-- Exact source-domain bilinear endpoint invisibility. -/
theorem routeUHardEdgePrimeJumpOddResponse_eq_zero_of_two_suzukiHlogAdmissions
    {n : ℕ} (hn : 2 ≤ n) {H K : ℝ → ℝ}
    (hg : MemLp (fun x : ℝ => x * H (x ^ (2 : ℕ))) 2 volume)
    (hk : MemLp (fun x : ℝ => x * K (x ^ (2 : ℕ))) 2 volume)
    (a : SuzukiPositiveAperture)
    (ha : a.1 = Real.log n / (4 * Real.pi))
    (qH qK : SuzukiHlogFormDomain a)
    (hqH : suzukiHlogWeightedToL2 qH.1 =
      ofRealLp (hg.toLp (fun x : ℝ => x * H (x ^ (2 : ℕ)))))
    (hqK : suzukiHlogWeightedToL2 qK.1 =
      ofRealLp (hk.toLp (fun x : ℝ => x * K (x ^ (2 : ℕ))))) :
    routeUHardEdgePrimeJumpOddResponse n H K = 0 := by
  apply routeUHardEdgePrimeJumpOddResponse_eq_zero_of_two_bandSupports hn hg hk
  · have hs := suzukiHlogFormDomain_fourier_bandSupport a qH
    rw [hqH] at hs
    simpa only [ha] using hs
  · have hs := suzukiHlogFormDomain_fourier_bandSupport a qK
    rw [hqK] at hs
    simpa only [ha] using hs

/-- The exact mixed odd form is unchanged across a prime wall on the entire admitted endpoint
band, not only on individual diagonals. -/
theorem routeUHardEdgeOddForm_log_nat_half_eq_incoming_of_two_suzukiHlogAdmissions
    {n : ℕ} (hn : 2 ≤ n) {H K : ℝ → ℝ}
    (hbase : IntegrableOn (fun u : ℝ =>
      u * (H u * K u) *
        routeUHardEdgeDensity (routeUHardEdgeIncomingAperture n) (Real.sqrt u) /
          Real.sqrt u) (Ioi 0))
    (hjump : IntegrableOn (fun u : ℝ =>
      u * (H u * K u) * routeUHardEdgePrimeJumpDensity n (Real.sqrt u) /
        Real.sqrt u) (Ioi 0))
    (hg : MemLp (fun x : ℝ => x * H (x ^ (2 : ℕ))) 2 volume)
    (hk : MemLp (fun x : ℝ => x * K (x ^ (2 : ℕ))) 2 volume)
    (a : SuzukiPositiveAperture)
    (ha : a.1 = Real.log n / (4 * Real.pi))
    (qH qK : SuzukiHlogFormDomain a)
    (hqH : suzukiHlogWeightedToL2 qH.1 =
      ofRealLp (hg.toLp (fun x : ℝ => x * H (x ^ (2 : ℕ)))))
    (hqK : suzukiHlogWeightedToL2 qK.1 =
      ofRealLp (hk.toLp (fun x : ℝ => x * K (x ^ (2 : ℕ))))) :
    routeUHardEdgeOddForm (Real.log n / 2) H K =
      routeUHardEdgeOddForm (routeUHardEdgeIncomingAperture n) H K := by
  rw [routeUHardEdgeOddForm_log_nat_half_eq_incoming_sub_primeJumpResponse
    hn H K hbase hjump,
    routeUHardEdgePrimeJumpOddResponse_eq_zero_of_two_suzukiHlogAdmissions
      hn hg hk a ha qH qK hqH hqK,
    sub_zero]

end RHTower
